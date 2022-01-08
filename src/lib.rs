
#[macro_use]
extern crate pest_derive;
extern crate derive_more;

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

    fn test_runner(path: &'static str) -> Result<()> {
        let mut db = database::Database::new();
        let mut builder = String::new();
        builder.push_str("tests/");
        let path = path.replace("_", "/");
        builder.push_str(path.as_str());
        builder.push_str(".ced");
        let path = Path::new(builder.as_str());
        db.load_module(path)
    }

    macro_rules! test_file_success {
        ($path_with_underscores:ident) => {
            #[test]
            fn $path_with_underscores() -> Result<()> {
                test_runner(stringify!($path_with_underscores))
            }
        }
    }

    test_file_success!(core_false);
    test_file_success!(core_true);
    test_file_success!(church_bool);
    test_file_success!(church_list);
    test_file_success!(church_nat);
    test_file_success!(church_unit);
    test_file_success!(church_vec);
}

