// Copyright (C) 2017 Red Hat, Inc.
//
// This file is part of bdcs-api-server.
//
// bdcs-api-server is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// bdcs-api-server is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with bdcs-api-server.  If not, see <http://www.gnu.org/licenses/>.

use db::*;
use rpm::*;
use rusqlite::Connection;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::slice::Iter;
use std::str::FromStr;
use itertools::Itertools;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Proposition {
    Obsoletes(Requirement, Requirement),
    Requires(Requirement, Requirement),
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Proposition::Obsoletes(ref left, ref right) => write!(f, "{} OBSOLETES {}", left, right),
            Proposition::Requires(ref left, ref right)  => write!(f, "{} REQUIRES {}", left, right)
        }
    }
}

// TODO might need to mess with the type for depsolve
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum DepAtom {
    GroupId(i64),
    Requirement(Requirement)
}

impl fmt::Display for DepAtom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DepAtom::GroupId(i)            => write!(f, "groupid={}", i),
            &DepAtom::Requirement(ref r)    => write!(f, "({})", r)
        }
    }
}

// TODO rename once this is all sorted out
#[derive(Debug, Clone)]
pub enum DepExpression {
    Atom(DepAtom),
    And(Box<Vec<DepExpression>>),
    Or(Box<Vec<DepExpression>>),
    Not(Box<DepExpression>)
}

impl fmt::Display for DepExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DepExpression::Atom(ref req)    => write!(f, "{}", req),
            &DepExpression::And(ref lst)     => { let strs: String = lst.iter().map(|x| x.to_string()).intersperse(String::from(" AND ")).collect();
                                                 write!(f, "{}", strs)
                                               },
            &DepExpression::Or(ref lst)      => { let strs: String = lst.iter().map(|x| x.to_string()).intersperse(String::from(" OR ")).collect();
                                                 write!(f, "{}", strs)
                                               },
            &DepExpression::Not(ref expr)    => write!(f, "NOT {}", expr)
        }
    }
}

// Given a requirement, find a list of groups providing it and return all of that as an expression
fn req_providers(conn: &Connection, arches: &Vec<String>, req: &Requirement, parents: &HashSet<i64>, cache: &mut HashMap<i64, DepExpression>) -> Result<DepExpression, String> {
    println!("req_providers: {} {}", req, parents.len());
    // helper function for converting a (Group, KeyVal) to Option<(group_id, Requirement)>
    fn provider_to_requirement(group: &Groups, kv: &KeyVal) -> Option<(i64, Requirement)> {
        let ext_val = match &kv.ext_value {
            &Some(ref ext_val) => ext_val,
            &None => return None
        };

        let requirement = match Requirement::from_str(ext_val.as_str()) {
            Ok(req) => req,
            Err(_)  => return None
        };

        Some((group.id, requirement))
    }

    // gather child requirements if necessary
    fn depclose_provider(conn: &Connection, arches: &Vec<String>, group_id: i64, parents: &HashSet<i64>, cache: &mut HashMap<i64, DepExpression>) -> Result<DepExpression, String> {
        let group_id_expr = DepExpression::Atom(DepAtom::GroupId(group_id));
        if parents.contains(&group_id) {
            println!("already closed over {}, skipping", group_id);
            Ok(group_id_expr)
        } else {
            let provider_expr = try!(depclose_package(conn, arches, group_id, parents, cache));
            cache.insert(group_id, provider_expr.clone());
            Ok(DepExpression::And(Box::new(vec![group_id_expr, provider_expr])))
        }
    }

    let mut group_providers = match get_provider_groups(conn, req.name.as_str()) {
        Ok(providers) => {
            // We have a vector of (Groups, KeyVal) pairs, not all of which match the
            // version portion of the requirement expression. We want the matching
            // providers as DepExpression values, with any unsolvable providers removed
            let providers_checked = providers.iter()
                                             // convert the provides expression to a Requirement and return a (group_id, Requirement) tuple
                                             .filter_map(|&(ref group, ref kv)| provider_to_requirement(group, kv))
                                             // filter out any that don't match version-wise
                                             .filter(|&(ref group_id, ref provider_req)| provider_req.satisfies(&req))
                                             // map the remaining providers to an expression, recursing to fetch the provider's requirements
                                             // any recursions that return Err unsatisfiable, so filter those out
                                             .filter_map(|(group_id, _)| depclose_provider(conn, arches, group_id, parents, cache).ok())
                                             .collect::<Vec<DepExpression>>();

            providers_checked
        },
        Err(e) => return Err(e.to_string())
    };

    // If the requirement looks like a filename, check for groups providing the file *in addition to* rpm-provide
    if req.name.starts_with('/') {
        let mut file_providers = match get_groups_filename(conn, req.name.as_str()) {
            Ok(groups) => {
                // Unlike group_providers, there are no versions to care about here
                groups.iter().filter_map(|ref group| depclose_provider(conn, arches, group.id, parents, cache).ok()).collect()
            },
            Err(e) => return Err(e.to_string())
        };
        group_providers.append(&mut file_providers);
    }

    // If there are no providers for the requirement, the requirement is unsatisfied, and that's an error
    if group_providers.is_empty() {
        Err(format!("Unable to satisfy requirement {}", req))
    } else {
        Ok(DepExpression::Or(Box::new(group_providers)))
    }
}

fn depclose_package(conn: &Connection, arches: &Vec<String>, group_id: i64, parent_groups: &HashSet<i64>, cache: &mut HashMap<i64, DepExpression>) -> Result<DepExpression, String> {
    println!("depclose_package: {}", group_id);

    // If this value is cached, return it
    if let Some(ref expr) = cache.get(&group_id) {
        return Ok((*expr).clone());
    }

    // TODO a functional hashmap or something similar would be super handy here
    // add this group to the parent groups, so that a cycle doesn't try to recurse on this group again
    let mut parent_groups_copy = parent_groups.clone();
    parent_groups_copy.insert(group_id);

    // Get all of the key/val based data we need
    let (group_provides, group_obsoletes, group_conflicts) = match get_groups_kv_group_id(conn, group_id) {
        Ok(group_key_vals) => {
            // map a key/value pair into a Requirement
            fn kv_to_expr(kv: &KeyVal) -> Result<DepExpression, String> {
                match &kv.ext_value {
                    &Some(ref ext_value) => Ok(DepExpression::Atom(DepAtom::Requirement(try!(Requirement::from_str(ext_value.as_str()))))),
                    &None                => Err(String::from("ext_value is not set"))
                }
            }

            fn kv_to_not_expr(kv: &KeyVal) -> Result<DepExpression, String> {
                Ok(DepExpression::Not(Box::new(kv_to_expr(kv)?)))
            }

            let mut group_provides = Vec::new();
            let mut group_obsoletes = Vec::new();
            let mut group_conflicts = Vec::new();

            for kv in group_key_vals.iter() {
                match kv.key_value.as_str() {
                    "rpm-provide" => group_provides.push(kv_to_expr(kv)),
                    "rpm-obsolete" => group_obsoletes.push(kv_to_not_expr(kv)),
                    "rpm-conflict" => group_conflicts.push(kv_to_not_expr(kv)),
                    _ => {}
                }
            }

            // Collect the Vec<Result<Expression, String>>s into a Result<Vec<Expression>, String>
            let group_provides_result: Result<Vec<DepExpression>, String> = group_provides.into_iter().collect();
            let group_obsoletes_result: Result<Vec<DepExpression>, String> = group_obsoletes.into_iter().collect();
            let group_conflicts_result: Result<Vec<DepExpression>, String> = group_conflicts.into_iter().collect();

            // unwrap the result or return the error
            (group_provides_result?, group_obsoletes_result?, group_conflicts_result?)
        },
        Err(e) => return Err(e.to_string())
    };

    // Collect the requirements
    let group_requirements = match get_requirements_group_id(conn, group_id) {
        Ok(requirements) => {
            // Map the data from the Requirements table into a rpm Requirement
            let gr_reqs: Vec<Requirement> = try!(requirements.iter().map(|r| Requirement::from_str(r.req_expr.as_str())).collect());

            // for each requirement, create a an expression of (requirement AND requirement_providers)
            let requirements_result: Result<Vec<DepExpression>, String> =
                gr_reqs.iter().map(|r| {
                    let providers = try!(req_providers(conn, arches, r, &parent_groups_copy, cache));
                    let req_expr  = DepExpression::Atom(DepAtom::Requirement(r.clone()));
                    Ok(DepExpression::And(Box::new(vec![req_expr, providers])))
                }).collect();

            try!(requirements_result)
        },
        Err(e) => return Err(e.to_string())
    };

    Ok(DepExpression::And(Box::new(vec![DepExpression::Atom(DepAtom::GroupId(group_id)),
                                        DepExpression::And(Box::new(group_provides)),
                                        DepExpression::And(Box::new(group_requirements)),
                                        DepExpression::And(Box::new(group_obsoletes)),
                                        DepExpression::And(Box::new(group_conflicts))])))
}

pub fn close_dependencies(conn: &Connection, arches: &Vec<String>, packages: &Vec<String>) -> Result<DepExpression, String> {
    let mut req_list = Vec::new();

    for p in packages.iter() {
        // TODO process all groups?
        match get_groups_name(conn, p, 0, 1) {
            Ok(groups) => req_list.push(depclose_package(conn, arches, groups[0].id, &HashSet::new(), &mut HashMap::new())?),
            Err(e)     => return Err(e.to_string())
        }
    }

    Ok(DepExpression::Or(Box::new(req_list)))
}
