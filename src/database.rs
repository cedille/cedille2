// TODO: Switch to daggy crate (assuming iterator yields a topological order) so that adding a new module doesn't
// require rebuilding and resorting the module graph every time


use std::io::prelude::*;
use std::fs::{self, File};
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use internment::Intern;
use anyhow::{Context, Result, anyhow};
use colored::*;
use thiserror::Error;

use crate::parser;
use crate::syntax;

type Symbol = Intern<String>;

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
}

#[derive(Debug)]
pub struct ModuleData {
    syntax: syntax::Module,
    text: String,
    imports: Vec<Symbol>,
    exports: HashMap<syntax::Id, Symbol>,
    last_modified: SystemTime,
}

#[derive(Debug)]
pub struct Database {
    pub modules: HashMap<Symbol, ModuleData>
}

impl Database {

    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
        }
    }

    fn loaded(&self, module: Symbol) -> bool {
        if let Some(data) = self.modules.get(&module) {
            let imports_loaded = data.imports.iter()
                .all(|i| self.loaded(*i));
            let current_modified = Path::new(module.as_ref())
                .metadata()
                .and_then(|m| m.modified())
                .unwrap_or_else(|_| SystemTime::now());
            imports_loaded && current_modified <= data.last_modified
        } else { false }
    }

    fn load_imports<P: AsRef<Path>>(&mut self, prefix: P, imports: impl Iterator<Item=P>, visited: HashSet<Symbol>) -> Result<Vec<Symbol>> {
        let mut result = vec![];
        for path in imports {
            let path = prefix.as_ref().join(path).with_extension("ced");
            let sym = self.load_module_with_visited(path, visited.clone())?;
            result.push(sym);
        }
        Ok(result)
    }

    fn load_module_with_visited<P: AsRef<Path>>(&mut self, path: P, mut visited: HashSet<Symbol>) -> Result<Symbol> {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Intern::from("")); }

        let canonical_path = path.canonicalize()
            .with_context(|| format!("Failed to canonicalize path {}", path.display()))?;
        let key = canonical_path.to_str()
            .ok_or(DatabaseError::NonUnicodePath { path:path.to_path_buf() })?;
        let sym = Intern::from(key);

        if visited.contains(&sym) {
            return Err(anyhow!(format!("Cycle in dependencies of module {}", key)));
        }
        visited.insert(sym);

        if self.loaded(sym) {
            println!("{} {}{}", "skipping file".dimmed(), key, "...".dimmed());
        } else {
            println!("{} {}{}", "loading file".dimmed(), key, "...".dimmed());
            /***
             * Parse the file to the dynamically typed AST
             ***/
            let metadata = path.metadata()
                .with_context(|| format!("Failed to extract metadata of path {}", path.display()))?;
            let last_modified = metadata.modified().unwrap_or_else(|_| SystemTime::now());
            let mut file = File::open(path)
                .with_context(|| format!("Failed to open file with path {}", path.display()))?;
            let mut buffer = Vec::new();
            file.read_to_end(&mut buffer)?;
            let text = String::from_utf8(buffer)?;
            let tree = parser::parse(&text)?;
            /***
             * Recurse through the files imports and load them first
             ***/
            let import_paths = parser::extract_imports(tree.clone()).into_iter()
                .map(|(start, end)| Path::new(&text[start..end]));
            let imports = self.load_imports(path.parent().unwrap(), import_paths, visited)?;
            /***
             * Construct the statically typed AST
             ***/
            let ctx = parser::Context::new(sym);
            let tree = parser::module((&text, ctx), tree);
            /***
             * Extract the modules exports
             ***/
            let exports = HashMap::new();
            /***
             * Elaborate and type check the statically typed AST
             ***/
            // TODO
            /***
             * Finish loading the module
             ***/
            let data = ModuleData {
                syntax: tree,
                text,
                imports,
                exports,
                last_modified,
            };
            self.modules.insert(sym, data);
        }
        Ok(sym)
    }

    pub fn load_module<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        self.load_module_with_visited(path, HashSet::new())
            .map(|_| ())
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<bool> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                if let Err(error) = self.load_module(path) {
                    println!("{}", error);
                }
            } else {
                self.load_dir(&path)?;
            }
        }
        Ok(true)
    }
}
