//! RPM Types and Functions
//!
//! ## Overview
//!
//! Various utilities for dealing with RPM data
//!

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

use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// Representation of epoch-version-release data
#[derive(Clone, Debug, Hash)]
pub struct EVR {
    pub epoch: Option<u32>,
    pub version: String,
    pub release: String
}

impl Ord for EVR {
    fn cmp(&self, other: &EVR) -> Ordering {
        // no epoch is equivalent to an epoch of 0
        let epoch_1 = self.epoch.unwrap_or(0);
        let epoch_2 = other.epoch.unwrap_or(0);

        if epoch_1 != epoch_2 {
            epoch_1.cmp(&epoch_2)
        } else if vercmp(self.version.as_str(), other.version.as_str()) != Ordering::Equal {
            vercmp(self.version.as_str(), other.version.as_str())
        } else {
            vercmp(self.release.as_str(), other.release.as_str())
        }
    }
}

impl PartialOrd for EVR {
    fn partial_cmp(&self, other: &EVR) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for EVR {
    fn eq(&self, other: &EVR) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for EVR {}

impl fmt::Display for EVR {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (self.epoch, self.release.as_str()) {
            (Some(e), "") => write!(f, "{}:{}", e, self.version),
            (Some(e), _)  => write!(f, "{}:{}-{}", e, self.version, self.release),
            (None, "")    => write!(f, "{}", self.version),
            (None, _)     => write!(f, "{}-{}", self.version, self.release)
        }
    }
}

impl FromStr for EVR {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // illegal characters for version and release
        fn illegal_char(c: char) -> bool {
            !(c.is_ascii() && (c.is_digit(10) || c.is_alphabetic() || "._+%{}~".contains(c)))
        }

        // If there's a colon, parse the part before it as an epoch
        let c_index = s.find(':');
        let (epoch, s_rest) = match c_index {
            Some(i) => {
                // Split the string into <epoch-string>, ":version-release", then split again
                // to remove the ':'. Parse the epoch as an unsigned int.
                let (epoch_str, colon_version) = s.split_at(i);
                let epoch = if let Ok(e) = epoch_str.parse::<u32>() {
                    Some (e)
                } else {
                    return Err(String::from("Epoch must be an unsigned int"));
                };
                let (_, s_rest) = colon_version.split_at(1);

                (epoch, s_rest)
            },
            None   => (None, s)
        };

        // version-release is separated by -
        let v_index = s_rest.find('-');
        let (s_version, s_release) = match v_index {
            // The version-release string can't start with '-'
            Some(0) => return Err(String::from("Missing version component")),
            Some(x) => {
                // Return the strings on either side of the hyphen
                let (s_version, hyphen_release) = s_rest.split_at(x);
                let (_, s_release) = hyphen_release.split_at(1);

                // Make sure the release isn't empty
                if s_release.is_empty() {
                    return Err(String::from("Missing release component"));
                }

                (s_version, s_release)
            },
            // No release, just version
            None    => (s_rest, "")
        };

        // check for illegal characters
        if s_version.contains(illegal_char) {
            return Err(String::from(format!("Illegal character in version {}", s_version)));
        }
        if s_release.contains(illegal_char) {
            return Err(String::from("Illegal character in release"));
        }

        Ok(EVR {epoch: epoch, version: String::from(s_version), release: String::from(s_release)})
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ReqOperator {
    GreaterThanEqual,
    GreaterThan,
    EqualTo,
    LessThanEqual,
    LessThan
}

impl fmt::Display for ReqOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            &ReqOperator::GreaterThanEqual => ">=",
            &ReqOperator::GreaterThan      => ">",
            &ReqOperator::EqualTo          => "=",
            &ReqOperator::LessThanEqual    => "<=",
            &ReqOperator::LessThan         => "<"
        })
    }
}

impl FromStr for ReqOperator {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            ">=" => Ok(ReqOperator::GreaterThanEqual),
            ">"  => Ok(ReqOperator::GreaterThan),
            "="  => Ok(ReqOperator::EqualTo),
            "<=" => Ok(ReqOperator::LessThanEqual),
            "<"  => Ok(ReqOperator::LessThan),
            _    => Err(String::from("Invalid operator"))
        }
    }
}

impl ReqOperator {
    // Match a ReqOperator with an Operator, so, e.g., >= matches > and =
    fn cmp(&self, o: Ordering) -> bool {
        match self {
            &ReqOperator::GreaterThanEqual => o == Ordering::Greater || o == Ordering::Equal,
            &ReqOperator::GreaterThan      => o == Ordering::Greater,
            &ReqOperator::EqualTo          => o == Ordering::Equal,
            &ReqOperator::LessThanEqual    => o == Ordering::Less || o == Ordering::Equal,
            &ReqOperator::LessThan         => o == Ordering::Less
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Requirement {
    pub name: String,
    pub expr: Option<(ReqOperator, EVR)>
}

impl fmt::Display for Requirement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr {
            Some((ref oper, ref evr)) => write!(f, "{} {} {}", self.name, oper, evr),
            None              => write!(f, "{}", self.name)
        }
    }
}

impl FromStr for Requirement {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut split_str = s.split_whitespace();
        let name = split_str.next().ok_or("Missing requirement name")?;
        let expr = match split_str.next() {
            Some(oper) => Some((oper.parse::<ReqOperator>()?,
                                split_str.next().ok_or("Missing version in requirement expression")?.parse::<EVR>()?)),
            None       => None
        };

        // Make sure that the whole string has been read
        match split_str.next() {
            None    => Ok(Requirement{name: String::from(name), expr: expr}),
            Some(_) => Err(String::from("Extra data after version"))
        }
    }
}

impl Requirement {
    pub fn satisfies(&self, requires: &Requirement) -> bool {
        // Names gotta match
        if self.name != requires.name {
            return false;
        }

        // unpack the expression parts
        // If either half is missing the expression, it's a match
        let (provides_operator, provides_evr, requires_operator, requires_evr) = 
            match (&self.expr, &requires.expr) {
                (&None, _) => return true,
                (_, &None) => return true,
                (&Some((ref provides_operator, ref provides_evr)), &Some((ref requires_operator, ref requires_evr))) =>
                    (provides_operator, provides_evr, requires_operator, requires_evr)
        };

        // Special case, oh boy!
        // If the epochs and versions match, one side has no release, and that side is =, >=, or <=, it's a match.
        // e.g. Provides: whatever <= 1.0, Requires: whatever >= 1.0-9
        if provides_evr.epoch.unwrap_or(0) == requires_evr.epoch.unwrap_or(0) &&
                provides_evr.version == requires_evr.version {
            if provides_operator.cmp(Ordering::Equal) && provides_evr.release == String::from("") {
                return true;
            }

            if requires_operator.cmp(Ordering::Equal) && requires_evr.release == String::from("") {
                return true;
            }
        }

        // Now unravel whether the ranges overlap
        match provides_evr.cmp(requires_evr) {
            // true if Provides: >[=] x || Requires: <[=] y
            Ordering::Less    => provides_operator.cmp(Ordering::Greater) || requires_operator.cmp(Ordering::Less),
                
            // true if Provides <[=] x || Requires: >[=] y
            Ordering::Greater => provides_operator.cmp(Ordering::Less) || requires_operator.cmp(Ordering::Greater),

            // true if the directions match
            Ordering::Equal   => (provides_operator.cmp(Ordering::Less) && requires_operator.cmp(Ordering::Less)) ||
                                 (provides_operator.cmp(Ordering::Equal) && requires_operator.cmp(Ordering::Equal)) ||
                                 (provides_operator.cmp(Ordering::Greater) && requires_operator.cmp(Ordering::Greater))
        }
    }
}

pub fn vercmp(v1: &str, v2: &str) -> Ordering {
    // RPM only cares about ASCII digits, ASCII alphabetic, and tilde
    fn is_version_char(&c: &char) -> bool {
        c.is_ascii() && (c.is_digit(10) || c.is_alphabetic() || c == '~')
    }
    fn not_version_char(&c: &char) -> bool {
        !is_version_char(&c)
    }

    // to avoid overflow, strip leading 0's, and then compare as string, longer string wins
    fn compare_ints(s1: &str, s2: &str) -> Ordering {
        fn is_zero(&c: &char) -> bool { c == '0' }
        let s1_stripped = s1.chars().skip_while(is_zero).collect::<String>();
        let s2_stripped = s2.chars().skip_while(is_zero).collect::<String>();
        let s1_len = s1_stripped.len();
        let s2_len = s2_stripped.len();

        if s1_len > s2_len {
            Ordering::Greater
        } else if s2_len > s1_len {
            Ordering::Less
        } else {
            s1_stripped.cmp(&s2_stripped)
        }
    }

    // Kind of like take_while but you can get to the rest of the string, too
    fn split_at_predicate<'a, P>(s: &'a String, p: P) -> (&'a str, &'a str)  where
            P: Fn(char) -> bool {
        let s_index = s.find(p);
        match s_index {
            Some(i) => s.split_at(i),
            None    => (s.as_str(), "")
        }
    }

    // Is there a way to compose ! and the is_* functions?
    fn not_is_digit(c: char) -> bool { 
        !(c.is_ascii() && c.is_digit(10))
    }
    fn not_is_alphabetic(c: char) -> bool {
        !(c.is_ascii() && c.is_alphabetic())
    }

    // Remove all leading characters we don't care about
    let v1_stripped = v1.chars().skip_while(not_version_char).collect::<String>();
    let v2_stripped = v2.chars().skip_while(not_version_char).collect::<String>();

    // If both strings are empty after stripping, the versions are equal
    if v1_stripped.is_empty() && v2_stripped.is_empty() {
        return Ordering::Equal;
    }

    // Tilde is less than everything, including the empty string
    if v1_stripped.starts_with('~') && v2_stripped.starts_with('~') {
        let (_, v1_rest) = v1_stripped.split_at(1);
        let (_, v2_rest) = v2_stripped.split_at(1);
        return vercmp(v1_rest, v2_rest);
    } else if v1_stripped.starts_with('~') {
        return Ordering::Less;
    } else if v2_stripped.starts_with('~') {
        return Ordering::Greater;
    } else if v1_stripped.is_empty() {
        return Ordering::Less;
    } else if v2_stripped.is_empty() {
        return Ordering::Greater;
    }

    // Now we have two definitely not-empty strings that do not start with ~
    // rpm compares strings by digit and non-digit components, so split out
    // the current component

    let v1_first = v1_stripped.clone().chars().nth(0).unwrap();
    let v2_first = v2_stripped.clone().chars().nth(0).unwrap();

    let ((v1_prefix, v1_rest), (v2_prefix, v2_rest)) =
        if v1_first.is_digit(10) {
            (split_at_predicate(&v1_stripped, not_is_digit),
             split_at_predicate(&v2_stripped, not_is_digit))
        } else {
            (split_at_predicate(&v1_stripped, not_is_alphabetic),
             split_at_predicate(&v2_stripped, not_is_alphabetic))
        };


    // Number segments are greater than non-number segments, so if we're looking at an alpha in v1
    // and a number in v2, v2 is greater. The opposite case, v1 being a number and v2 being a non-number,
    // is handled by v1_prefix being empty and therefore less in the eyes of compare_ints.
    if !v1_first.is_digit(10) && v2_first.is_digit(10) {
        Ordering::Less
    } else if v1_first.is_digit(10) {
        match compare_ints(v1_prefix, v2_prefix) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => vercmp(v1_rest, v2_rest)
        }
    } else {
        match v1_prefix.cmp(v2_prefix) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => vercmp(v1_rest, v2_rest)
        }
    }
}

#[test]
fn test_evr_ord() -> () {
    fn reverse_ord(o: Ordering) -> Ordering {
        match o {
            Ordering::Greater => Ordering::Less,
            Ordering::Less    => Ordering::Greater,
            Ordering::Equal   => Ordering::Equal
        }
    }

    let evr_test_cases = [
        (EVR {epoch: None, version: String::from("1.0"), release: String::from("1")},    EVR {epoch: None, version: String::from("1.0"), release: String::from("1")}, Ordering::Equal),
        (EVR {epoch: Some(0), version: String::from("1.0"), release: String::from("1")}, EVR {epoch: None, version: String::from("1.0"), release: String::from("1")}, Ordering::Equal),
        (EVR {epoch: Some(1), version: String::from("1.0"), release: String::from("1")}, EVR {epoch: None, version: String::from("1.0"), release: String::from("1")}, Ordering::Greater),
        (EVR {epoch: None, version: String::from("1.0"), release: String::from("1")},    EVR {epoch: None, version: String::from("1.1"), release: String::from("1")}, Ordering::Less),
        (EVR {epoch: None, version: String::from("1.0"), release: String::from("1")},    EVR {epoch: None, version: String::from("1.0"), release: String::from("2")}, Ordering::Less),

        // from hawkey's tests/test_subject.c
        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("11.fc100")}, EVR {epoch: Some(3),  version: String::from("3.6.9"), release: String::from("11.fc100")}, Ordering::Greater),
        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("11.fc100")}, EVR {epoch: Some(11), version: String::from("3.6.9"), release: String::from("11.fc100")}, Ordering::Less),
        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("11.fc100")}, EVR {epoch: Some(8),  version: String::from("7.0"),   release: String::from("11.fc100")}, Ordering::Less),
        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("11.fc100")}, EVR {epoch: Some(8),  version: String::from(""),      release: String::from("11.fc100")}, Ordering::Greater),
        (EVR {epoch: Some(8), version: String::from(""),      release: String::from("11.fc100")}, EVR {epoch: Some(8),  version: String::from(""),      release: String::from("11.fc100")}, Ordering::Equal)
    ];

    for &(ref e1, ref e2, result) in evr_test_cases.iter() {
        // Test both the ordering and the reverse
        assert_eq!(e1.cmp(&e2), result);
        assert_eq!(e2.cmp(&e1), reverse_ord(result));

        // Test that Eq works
        match result {
            Ordering::Equal => assert_eq!(e1, e2),
            _               => assert!(e1 != e2)
        };
    };
}

#[test]
fn test_evr_format() -> () {
    let show_test_cases = [
        (EVR {epoch: None, version: String::from("1.0"), release: String::from("1")},    "1.0-1"),
        (EVR {epoch: Some(0), version: String::from("1.0"), release: String::from("1")}, "0:1.0-1"),
        (EVR {epoch: Some(1), version: String::from("1.0"), release: String::from("1")}, "1:1.0-1"),

        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("11.fc100")}, "8:3.6.9-11.fc100"),
        
        // empty versions aren't allowed on the parse side, but make sure they at least don't blow up
        (EVR {epoch: None, version: String::from(""), release: String::from("")},                 ""),
        (EVR {epoch: Some(8), version: String::from(""), release: String::from("")},              "8:"),
        (EVR {epoch: None, version: String::from(""), release: String::from("11.fc100")},         "-11.fc100"),
        (EVR {epoch: Some(8), version: String::from(""), release: String::from("11.fc100")},      "8:-11.fc100"),
        (EVR {epoch: None, version: String::from("3.6.9"), release: String::from("")},            "3.6.9"),
        (EVR {epoch: Some(8), version: String::from("3.6.9"), release: String::from("")},         "8:3.6.9"),
    ];

    for &(ref e1, s) in show_test_cases.iter() {
        assert_eq!(format!("{}", e1), s);
    };
}

#[cfg(test)]
mod test_evr_parse {
    use rpm::EVR;
    fn parse_evr(s: &str) -> EVR {
        match s.parse::<EVR>() {
            Ok(evr)  => evr,
            Err(err) => panic!("Failed to parse {}: {}", s, err)
        }
    }

    #[test]
    fn good_tests() -> () {
        let parse_test_cases = [
            ("1.0-11.fc100",   EVR {epoch: None, version: String::from("1.0"), release: String::from("11.fc100")}),
            ("0:1.0-11.fc100", EVR {epoch: Some(0), version: String::from("1.0"), release: String::from("11.fc100")}),
            ("8:1.0-11.fc100", EVR {epoch: Some(8), version: String::from("1.0"), release: String::from("11.fc100")}),
            ("1.0",            EVR {epoch: None,    version: String::from("1.0"), release: String::from("")}),
            ("8:1.0",          EVR {epoch: Some(8), version: String::from("1.0"), release: String::from("")}),
        ];

        for &(s, ref e1) in parse_test_cases.iter() {
            assert!(e1.eq(&parse_evr(s)));
        };
    }

    #[test]
    #[should_panic]
    fn missing_epoch() -> () {
        parse_evr(":1.0-11.fc100");
    }

    #[test]
    #[should_panic]
    fn missing_version() -> () {
        parse_evr("0:-11.fc100");
    }

    #[test]
    #[should_panic]
    fn missing_release() -> () {
        parse_evr("0:1.0-");
    }

    #[test]
    #[should_panic]
    fn invalid_epoch_1() -> () {
        // can't be negative
        parse_evr("-1:1.0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_epoch_2() -> () {
        // non numeric
        parse_evr("A:1.0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_epoch_3() -> () {
        // overflow u32
        parse_evr("8589934592:1.0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_version_1() -> () {
        parse_evr("0:1.0:0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_version_2() -> () {
        parse_evr("0:1.0&0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_version_3() -> () {
        parse_evr("0:1.0🌮0-100.fc11");
    }

    #[test]
    #[should_panic]
    fn invalid_release_1() -> () {
        parse_evr("0:1.0-100.fc:11");
    }

    #[test]
    #[should_panic]
    fn invalid_release_2() -> () {
        parse_evr("0:1.0-100.fc&11");
    }

    #[test]
    #[should_panic]
    fn invalid_release_3() -> () {
        parse_evr("0:1.0-100.fc🌮11");
    }
}

#[test]
fn test_operator_display() -> () {
    assert_eq!(format!("{}", ReqOperator::GreaterThanEqual), ">=");
    assert_eq!(format!("{}", ReqOperator::GreaterThan),      ">");
    assert_eq!(format!("{}", ReqOperator::EqualTo),          "=");
    assert_eq!(format!("{}", ReqOperator::LessThanEqual),    "<=");
    assert_eq!(format!("{}", ReqOperator::LessThan),         "<");
}

#[cfg(test)]
mod test_reqoperator_parse {
    use rpm::ReqOperator;
    fn parse_reqoperator(s: &str) -> ReqOperator {
        match s.parse::<ReqOperator>() {
            Ok(evr)  => evr,
            Err(err) => panic!("Failed to parse {}: {}", s, err)
        }
    }

    #[test]
    fn good_tests() -> () {
        assert_eq!(parse_reqoperator(">="), ReqOperator::GreaterThanEqual);
        assert_eq!(parse_reqoperator(">"),  ReqOperator::GreaterThan);
        assert_eq!(parse_reqoperator("="),  ReqOperator::EqualTo);
        assert_eq!(parse_reqoperator("<="), ReqOperator::LessThanEqual);
        assert_eq!(parse_reqoperator("<"),  ReqOperator::LessThan);
    }

    #[test]
    #[should_panic]
    fn empty_test() -> () {
        parse_reqoperator("");
    }

    #[test]
    #[should_panic]
    fn extra_data() -> () {
        parse_reqoperator(">=🌮");
    }

    #[test]
    #[should_panic]
    fn invalid_data() -> () {
        parse_reqoperator("🌮");
    }
}

#[test]
fn test_reqoperator_cmp() -> () {
    assert!(ReqOperator::GreaterThanEqual.cmp(Ordering::Greater));
    assert!(ReqOperator::GreaterThanEqual.cmp(Ordering::Equal));
    assert!(!ReqOperator::GreaterThanEqual.cmp(Ordering::Less));

    assert!(ReqOperator::GreaterThan.cmp(Ordering::Greater));
    assert!(!ReqOperator::GreaterThan.cmp(Ordering::Equal));
    assert!(!ReqOperator::GreaterThan.cmp(Ordering::Less));

    assert!(!ReqOperator::EqualTo.cmp(Ordering::Greater));
    assert!(ReqOperator::EqualTo.cmp(Ordering::Equal));
    assert!(!ReqOperator::EqualTo.cmp(Ordering::Less));

    assert!(!ReqOperator::LessThanEqual.cmp(Ordering::Greater));
    assert!(ReqOperator::LessThanEqual.cmp(Ordering::Equal));
    assert!(ReqOperator::LessThanEqual.cmp(Ordering::Less));

    assert!(!ReqOperator::LessThan.cmp(Ordering::Greater));
    assert!(!ReqOperator::LessThan.cmp(Ordering::Equal));
    assert!(ReqOperator::LessThan.cmp(Ordering::Less));
}

#[test]
fn test_requirement_format() -> () {
    // assume if one operator works they all work
    let format_test_cases = [
        (Requirement {name: String::from("libthing"), expr: None}, "libthing"),
        (Requirement {name: String::from("libthing"), expr: Some((ReqOperator::GreaterThanEqual, EVR {epoch: None, version: String::from("1.0"), release: String::from("1")}))}, "libthing >= 1.0-1"),
    ];

    for &(ref r, s) in format_test_cases.iter() {
        assert_eq!(format!("{}", r), s);
    }
}

#[test]
fn test_requirement_parse() -> () {
    let parse_test_cases = [
        (Requirement {name: String::from("libthing"), expr: None}, "libthing"),
        (Requirement {name: String::from("libthing"), expr: Some((ReqOperator::GreaterThanEqual, EVR {epoch: None, version: String::from("1.0"), release: String::from("1")}))}, "libthing >= 1.0-1"),
    ];

    for &(ref r, s) in parse_test_cases.iter() {
        assert_eq!(&s.parse::<Requirement>().unwrap(), r);
    }
}

#[test]
fn satisfies_tests() -> () {
    // provides, requires, true/false
    let test_cases = [
        ("no", "match", false),

        ("thing",          "thing",          true),
        ("thing",          "thing >= 1.0-1", true),
        ("thing >= 1.0-1", "thing",          true),
        
        ("thing = 1.0-1",  "thing = 1.0-1",  true),
        ("thing = 1.0-1",  "thing >= 1.0-1", true),
        ("thing = 1.0-1",  "thing > 1.0-1",  false),
        ("thing = 1.0-1",  "thing < 1.0-1",  false),
        ("thing = 1.0-1",  "thing <= 1.0-1", true),

        ("thing = 1.0",    "thing = 1.0-9",   true),
        ("thing = 1.0",    "thing < 1.0-9",   true),
        ("thing = 1.0",    "thing <= 1.0-9",  true),
        ("thing = 1.0",    "thing <= 1.0-9",  true),
        ("thing = 1.0",    "thing = 1.0-9",   true),

        ("thing <= 1.0",   "thing = 1.0-9",   true),
        ("thing <= 1.0",   "thing < 1.0-9",   true),
        ("thing <= 1.0",   "thing <= 1.0-9",  true),
        ("thing <= 1.0",   "thing <= 1.0-9",  true),
        ("thing <= 1.0",   "thing = 1.0-9",   true),

        ("thing >= 1.0",   "thing = 1.0-9",   true),
        ("thing >= 1.0",   "thing < 1.0-9",   true),
        ("thing >= 1.0",   "thing <= 1.0-9",  true),
        ("thing >= 1.0",   "thing <= 1.0-9",  true),
        ("thing >= 1.0",   "thing = 1.0-9",   true),

        ("thing = 1.0-9",  "thing = 1.0-9",   true),
        ("thing < 1.0-9",  "thing = 1.0-9",   false),
        ("thing <= 1.0-9", "thing = 1.0-9",   true),
        ("thing > 1.0-9",  "thing = 1.0-9",   false),
        ("thing >= 1.0-9", "thing = 1.0-9",   true),

        ("thing >= 1.0-1", "thing = 1.0-1",  true),
        ("thing >= 1.0-1", "thing >= 1.0-1", true),
        ("thing >= 1.0-1", "thing > 1.0-1",  true),
        ("thing >= 1.0-1", "thing < 1.0-1",  false),
        ("thing >= 1.0-1", "thing <= 1.0-1", true),

        ("thing > 1.0-1",  "thing = 1.0-1",  false),
        ("thing > 1.0-1",  "thing >= 1.0-1", true),
        ("thing > 1.0-1",  "thing > 1.0-1",  true),
        ("thing > 1.0-1",  "thing < 1.0-1",  false),
        ("thing > 1.0-1",  "thing <= 1.0-1", false),

        ("thing < 1.0-1",  "thing = 1.0-1",  false),
        ("thing < 1.0-1",  "thing >= 1.0-1", false),
        ("thing < 1.0-1",  "thing > 1.0-1",  false),
        ("thing < 1.0-1",  "thing < 1.0-1",  true),
        ("thing < 1.0-1",  "thing <= 1.0-1", true),

        ("thing <= 1.0-1", "thing = 1.0-1",  true),
        ("thing <= 1.0-1", "thing >= 1.0-1", true),
        ("thing <= 1.0-1", "thing > 1.0-1",  false),
        ("thing <= 1.0-1", "thing < 1.0-1",  true),
        ("thing <= 1.0-1", "thing <= 1.0-1", true),

        ("thing = 9.0",    "thing = 1.0-1",  false),
        ("thing = 9.0",    "thing >= 1.0-1", true),
        ("thing = 9.0",    "thing > 1.0-1",  true),
        ("thing = 9.0",    "thing <= 1.0-1", false),
        ("thing = 9.0",    "thing < 1.0-1",  false),

        ("thing < 9.0",    "thing = 1.0-1",  true),
        ("thing < 9.0",    "thing >= 1.0-1", true),
        ("thing < 9.0",    "thing > 1.0-1",  true),
        ("thing < 9.0",    "thing <= 1.0-1", true),
        ("thing < 9.0",    "thing < 1.0-1",  true),

        ("thing <= 9.0",   "thing = 1.0-1",  true),
        ("thing <= 9.0",   "thing >= 1.0-1", true),
        ("thing <= 9.0",   "thing > 1.0-1",  true),
        ("thing <= 9.0",   "thing <= 1.0-1", true),
        ("thing <= 9.0",   "thing < 1.0-1",  true),

        ("thing > 9.0",    "thing = 1.0-1",  false),
        ("thing > 9.0",    "thing >= 1.0-1", true),
        ("thing > 9.0",    "thing > 1.0-1",  true),
        ("thing > 9.0",    "thing <= 1.0-1", false),
        ("thing > 9.0",    "thing < 1.0-1",  false),

        ("thing >= 9.0",   "thing = 1.0-1",  false),
        ("thing >= 9.0",   "thing >= 1.0-1", true),
        ("thing >= 9.0",   "thing > 1.0-1",  true),
        ("thing >= 9.0",   "thing <= 1.0-1", false),
        ("thing >= 9.0",   "thing < 1.0-1",  false),

        ("thing = 1.0",    "thing = 9.0-1",  false),
        ("thing = 1.0",    "thing >= 9.0-1", false),
        ("thing = 1.0",    "thing > 9.0-1",  false),
        ("thing = 1.0",    "thing <= 9.0-1", true),
        ("thing = 1.0",    "thing < 9.0-1",  true),

        ("thing < 1.0",    "thing = 9.0-1",  false),
        ("thing < 1.0",    "thing >= 9.0-1", false),
        ("thing < 1.0",    "thing > 9.0-1",  false),
        ("thing < 1.0",    "thing <= 9.0-1", true),
        ("thing < 1.0",    "thing < 9.0-1",  true),

        ("thing <= 1.0",   "thing = 9.0-1",  false),
        ("thing <= 1.0",   "thing >= 9.0-1", false),
        ("thing <= 1.0",   "thing > 9.0-1",  false),
        ("thing <= 1.0",   "thing <= 9.0-1", true),
        ("thing <= 1.0",   "thing < 9.0-1",  true),

        ("thing >= 1.0",   "thing = 9.0-1",  true),
        ("thing >= 1.0",   "thing >= 9.0-1", true),
        ("thing >= 1.0",   "thing > 9.0-1",  true),
        ("thing >= 1.0",   "thing <= 9.0-1", true),
        ("thing >= 1.0",   "thing < 9.0-1",  true),

        ("thing > 1.0",    "thing = 9.0-1",  true),
        ("thing > 1.0",    "thing >= 9.0-1", true),
        ("thing > 1.0",    "thing > 9.0-1",  true),
        ("thing > 1.0",    "thing <= 9.0-1", true),
        ("thing > 1.0",    "thing < 9.0-1",  true),
    ];

    for &(s1, s2, result) in test_cases.iter() {
        let r1 = s1.parse::<Requirement>().unwrap();
        let r2 = s2.parse::<Requirement>().unwrap();
        if r1.satisfies(&r2) != result {
            panic!("Failed to satisfy: Provides: {}, Requires: {}, result: {}", r1, r2, result);
        }
    }
}

#[test]
fn test_vercmp() -> () {
    // These are from tests/rpmvercmp.at in the rpm source
    let vercmp_test_cases = [
        ("1.0", "1.0", Ordering::Equal),
        ("1.0", "2.0", Ordering::Less),
        ("2.0", "1.0", Ordering::Greater),

        ("2.0.1", "2.0.1", Ordering::Equal),
        ("2.0", "2.0.1", Ordering::Less),
        ("2.0.1", "2.0", Ordering::Greater),

        ("2.0.1a", "2.0.1a", Ordering::Equal),
        ("2.0.1a", "2.0.1", Ordering::Greater),
        ("2.0.1", "2.0.1a", Ordering::Less),

        ("5.5p1", "5.5p1", Ordering::Equal),
        ("5.5p1", "5.5p2", Ordering::Less),
        ("5.5p2", "5.5p1", Ordering::Greater),

        ("5.5p10", "5.5p10", Ordering::Equal),
        ("5.5p1", "5.5p10", Ordering::Less),
        ("5.5p10", "5.5p1", Ordering::Greater),

        ("10xyz", "10.1xyz", Ordering::Less),
        ("10.1xyz", "10xyz", Ordering::Greater),

        ("xyz10", "xyz10", Ordering::Equal),
        ("xyz10", "xyz10.1", Ordering::Less),
        ("xyz10.1", "xyz10", Ordering::Greater),

        ("xyz.4", "xyz.4", Ordering::Equal),
        ("xyz.4", "8", Ordering::Less),
        ("8", "xyz.4", Ordering::Greater),
        ("xyz.4", "2", Ordering::Less),
        ("2", "xyz.4", Ordering::Greater),

        ("5.5p2", "5.6p1", Ordering::Less),
        ("5.6p1", "5.5p2", Ordering::Greater),

        ("5.6p1", "6.5p1", Ordering::Less),
        ("6.5p1", "5.6p1", Ordering::Greater),

        ("6.0.rc1", "6.0", Ordering::Greater),
        ("6.0", "6.0.rc1", Ordering::Less),

        ("10b2", "10a1", Ordering::Greater),
        ("10a2", "10b2", Ordering::Less),
        ("1.0aa", "1.0aa", Ordering::Equal),
        ("1.0a", "1.0aa", Ordering::Less),
        ("1.0aa", "1.0a", Ordering::Greater),

        ("10.0001", "10.0001", Ordering::Equal),
        ("10.0001", "10.1", Ordering::Equal),
        ("10.1", "10.0001", Ordering::Equal),
        ("10.0001", "10.0039", Ordering::Less),
        ("10.0039", "10.0001", Ordering::Greater),

        ("4.999.9", "5.0", Ordering::Less),
        ("5.0", "4.999.9", Ordering::Greater),

        ("20101121", "20101121", Ordering::Equal),
        ("20101121", "20101122", Ordering::Less),
        ("20101122", "20101121", Ordering::Greater),

        ("2_0", "2_0", Ordering::Equal),
        ("2.0", "2_0", Ordering::Equal),
        ("2_0", "2.0", Ordering::Equal),

        ("a", "a", Ordering::Equal),
        ("a+", "a+", Ordering::Equal),
        ("a+", "a_", Ordering::Equal),
        ("a_", "a+", Ordering::Equal),
        ("+a", "+a", Ordering::Equal),
        ("+a", "_a", Ordering::Equal),
        ("_a", "+a", Ordering::Equal),
        ("+_", "+_", Ordering::Equal),
        ("_+", "+_", Ordering::Equal),
        ("_+", "_+", Ordering::Equal),
        ("+", "_", Ordering::Equal),
        ("_", "+", Ordering::Equal),

        ("1.0~rc1", "1.0~rc1", Ordering::Equal),
        ("1.0~rc1", "1.0", Ordering::Less),
        ("1.0", "1.0~rc1", Ordering::Greater),
        ("1.0~rc1", "1.0~rc2", Ordering::Less),
        ("1.0~rc2", "1.0~rc1", Ordering::Greater),
        ("1.0~rc1~git123", "1.0~rc1~git123", Ordering::Equal),
        ("1.0~rc1~git123", "1.0~rc1", Ordering::Less),
        ("1.0~rc1", "1.0~rc1~git123", Ordering::Greater)
    ];

    for &(s1, s2, result) in vercmp_test_cases.iter() {
        assert_eq!(vercmp(&s1, &s2), result);
    };
}
