
use std::io::prelude::*;
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::collections::HashMap;

use anyhow::Result;
use colored::*;

use crate::parser;
use crate::syntax;

pub struct Database {
    modules: HashMap<PathBuf, (String, syntax::Module)>
}

impl Database {

    pub fn new() -> Database {
        Database { 
            modules: HashMap::new()
        }
    }

    pub fn load_file(&mut self, path: &Path) -> Result<bool> {
        let mut file = File::open(path)?;
        if let Some(ext) = path.extension() {
            if ext.to_string_lossy() == "ced" {
                println!("{} {}{}", "loading file".dimmed(), path.display(), "...".dimmed());
                let mut buffer = Vec::new();
                file.read_to_end(&mut buffer)?;
                let text = String::from_utf8(buffer)?;
                let tree = parser::parse(text.as_str())?;
                /* println!("{}", tree); */
                let tree = parser::module(tree);
                // TODO: Parse and check text
            }
        }
        Ok(true)
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<bool> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                if let Err(error) = self.load_file(&path) {
                    println!("{}", error);
                }
            } else {
                self.load_dir(&path)?;
            }
        }
        Ok(true)
    }
}