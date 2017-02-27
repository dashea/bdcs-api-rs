extern crate bdcs;
extern crate r2d2;
extern crate r2d2_sqlite;
extern crate rusqlite;

use bdcs::depclose::*;
use bdcs::depsolve::*;
use bdcs::rpm::Requirement;

use r2d2_sqlite::SqliteConnectionManager;
use std::collections::{HashMap, HashSet};
use std::env;
use std::process::exit;
use std::str::FromStr;

fn main() {
    let mut argv: Vec<String> = env::args().collect();
    if argv.len() < 3 {
        println!("depclose metadata.db RPM [RPM...]");
    }

    // Remove the program, grab the database.
    argv.remove(0);
    let db = argv.remove(0);

    let cfg = r2d2::Config::builder().build();
    let mgr = SqliteConnectionManager::new(db.as_str());
    let pool = r2d2::Pool::new(cfg, mgr).unwrap();

    let conn = pool.get().unwrap();

    let depexpr = match close_dependencies(&conn, &vec!(String::from("x86_64")), &argv) {
        Err(e)    => { println!("Error: {}", e);
                       exit(1);
                     }
        Ok(expr)  => expr
    };
    println!("Deps: {}", depexpr);

//    let (props, provided_by_dict) = match close_dependencies(&conn, &vec!(String::from("x86_64")), &argv) {
//        Err(e)  => { println!("Error: {}", e);
//                     exit(1);
//                   }
//        Ok(tup) => tup
//    };

//     let mut exprset = HashSet::new();
// 
//     // Add boolean expressions for each thing that was requested to be installed.
//     for thing in argv {
//         exprset.insert(Expression::Atom(Requirement::from_str(thing.as_str()).unwrap()));
//     }
// 
//     // Convert all the Propositions given by close_dependencies into boolean expressions
//     // that can be solved.  This also involves translating Provides into what actually
//     // provides them.
//     for p in props {
//         if let Some(x) = proposition_to_expression(p, &provided_by_dict) {
//             exprset.insert(x);
//         }
//     }
// 
//     let mut assignments = HashMap::new();
//     let mut exprs = exprset.into_iter().collect();
//     unit_propagation(&mut exprs, &mut assignments);
// 
//     for a in assignments { println!("{:?}", a) }
//     for x in exprs { println!("{}", x) }
}
