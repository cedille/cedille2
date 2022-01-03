
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

    fn test_runner(components: Vec<&'static str>, id: &'static str, is_dir: bool) -> Result<()> {
        let mut db = database::Database::new();
        let mut builder = String::new();
        for s in components.iter() {
            builder.push_str(s);
            builder.push('/');
        }
        builder.push_str(id);
        if !is_dir { builder.push_str(".ced"); }
        let path = Path::new(builder.as_str());
        if is_dir { db.load_dir(path) }
        else { db.load_module(path) }
    }

    macro_rules! test_file_success {
        ([$($component:ident),*], $id:ident) => {
            #[test]
            fn $id() -> Result<()> {
                test_runner(vec![$(stringify!($component),)*], stringify!($id), false)
            }
        }
    }

    macro_rules! test_dir_success {
        ([$($component:ident),*], $id:ident) => {
            #[test]
            fn $id() -> Result<()> {
                test_runner(vec![$(stringify!($component),)*], stringify!($id), true)
            }
        }
    }

    test_file_success!([tests], church);

    test_dir_success!([lib], core);
}

