
use std::io::prelude::*;
use std::fs::{self, File};
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use internment::Intern;
use anyhow::{Context, Result, anyhow};
use colored::*;
use thiserror::Error;

use crate::lang::parser;
use crate::lang::syntax;
use crate::kernel::term;
use crate::lang::elaborator;
use crate::lang::resolver;

type Symbol = Intern<String>;

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vec<Intern<String>>,
    pub name: Intern<String>,
}

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
}

#[derive(Debug)]
pub struct ImmediateExports {
    namespace_args: Vec<(syntax::Mode, syntax::Term)>,
    def: HashSet<syntax::Term>
}

#[derive(Debug)]
pub struct ModuleData {
    text: String,
    imports: Vec<Symbol>,
    exports: HashMap<Option<Symbol>, ImmediateExports>,
    params: Vec<syntax::Parameter>,
    last_modified: SystemTime,
}

#[derive(Debug)]
pub struct Database {
    pub modules: HashMap<Symbol, ModuleData>,
    pub defs: HashSet<Id>,
}

impl Database {

    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            defs: HashSet::new(),
        }
    }

    pub fn lookup(&self, id: &Id) -> Option<&syntax::Term> {
        todo!()
    }

    pub fn normal_from(&mut self, id: Id) -> syntax::Term {
        todo!()
/*         let (mut result, is_normal) = {
            let module = self.modules.get_mut(id.module.as_ref())
                .unwrap_or_else(|| panic!("Precondition failed: Module at path {} is missing", id.module));
            if let Some(normal) = module.normals.get(&id) {
                (normal.clone(), true)
            } else {
                let term = module.kernel.decls.iter()
                    .find_map(|decl| match decl {
                        kernel::Decl::Type(kernel::DefineType { id:id2, body, .. }) => {
                            if id == *id2 { Some(kernel::TermOrType::Type(*body.clone())) }
                            else { None }
                        },
                        kernel::Decl::Term(kernel::DefineTerm { id:id2, body, .. }) => {
                            if id == *id2 { Some(kernel::TermOrType::Term(*body.clone())) }
                            else { None }
                        },
                    })
                    .unwrap_or_else(|| panic!("Precondition failed: Id {:?} is not defined", id));
                (term, false)
            }
        };
        if !is_normal {
            use kernel::TermOrType::*;
            result = match result {
                Type(t) => Type(kernel::Type::normalize(self, t, None)),
                Term(t) => Term(kernel::Term::normalize(self, t, None))
            };
            let module = self.modules.get_mut(id.module.as_ref())
                .unwrap_or_else(|| panic!("Precondition failed: Module at path {} is missing", id.module));
            module.normals.insert(id, result.clone());
        }
        result */
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
            let mut tree = parser::module(tree);
            resolver::resolve(&mut tree, self);
            /***
             * Elaborate and type check the statically typed AST
             ***/
            let kernel = elaborator::elaborate(self, &tree);
            /***
             * Extract the modules exports
             ***/
            /* let exports = HashMap::new(); */
            /***
             * Finish loading the module
             ***/
/*             let data = ModuleData {
                syntax: tree,
                kernel,
                text,
                imports,
                exports,
                normals: HashMap::new(),
                last_modified,
            };
            self.modules.insert(sym, data); */
        }
        Ok(sym)
    }

    pub fn load_module<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        self.load_module_with_visited(path, HashSet::new()).map(|_| ())
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
