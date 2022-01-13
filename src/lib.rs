
#[macro_use]
extern crate pest_derive;
extern crate derive_more;
#[macro_use]
extern crate if_chain;

use paste::paste;

pub mod repl;
mod database;
mod common;
mod kernel;
mod lang;

#[cfg(test)]
mod tests {
    use std::path::Path;
    use anyhow::Result;
    use super::*;

    fn test_runner(path: &'static str, expected_success: bool) -> Result<()> {
        let mut db = database::Database::new();
        let mut builder = String::new();
        if expected_success { builder.push_str("tests/success/"); }
        else { builder.push_str("tests/failure/"); }
        let path = path.replace("_", "/");
        builder.push_str(path.as_str());
        builder.push_str(".ced");
        let path = Path::new(builder.as_str());
        let result = db.load_module_from_path(path);
        if expected_success { result.map(|_| ()) }
        else {
            let error = ||
                Err(anyhow::anyhow!("File succeeded when it should have failed."));
            result.err().map_or_else(error, |e| { eprintln!("{:?}", e); Ok(()) })
        }
    }

    macro_rules! test_file_success {
        ($path_with_underscores:ident) => {
            paste! {
            #[test]
                fn [<success_$path_with_underscores>]() -> Result<()> {
                    test_runner(stringify!($path_with_underscores), true)
                }
            }
        }
    }

    macro_rules! test_file_failure {
        ($path_with_underscores:ident) => {
            paste! {
                #[test]
                fn [<failure_$path_with_underscores>]() -> Result<()> {
                    test_runner(stringify!($path_with_underscores), false)
                }
            }
        }
    }

    test_file_success!(core_false);
    test_file_success!(core_true);

    test_file_success!(church_bool);
    test_file_success!(church_list);
    test_file_success!(church_nat);
    test_file_success!(church_unit);
    test_file_success!(church_inductive_unit);
    test_file_success!(church_vec);

    test_file_success!(module_unqualified);
    test_file_success!(module_qualified);
    test_file_success!(module_mixed);
    test_file_success!(module_transitive);
    test_file_success!(module_transitive2);
    test_file_success!(module_transitive3);
    test_file_success!(module_transitive4);

    test_file_failure!(core_intersect);

    test_file_failure!(module_cycle);
    test_file_failure!(module_mixed);
    test_file_failure!(module_doubleimport);
    test_file_failure!(module_redefined);
    test_file_failure!(module_redefined2);
}

