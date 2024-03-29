
use std::fs::{self};
use std::io::prelude::*;
use std::path::Path;
use std::borrow::Cow::{self, Borrowed, Owned};

use anyhow::Result;
use thiserror::Error;
use clap::crate_version;
use colored::*;
use directories::ProjectDirs;

use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::config::OutputStreamType;
use rustyline::error::ReadlineError;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{Cmd, CompletionType, Config, Context, Editor, Helper, KeyEvent, Modifiers};

use cedille2_lang::error::CedilleError;
use cedille2_lang::database::DatabaseExt;
use cedille2_core::database::Database;
use cedille2_core::parser;

const REPL_HISTORY_LIMIT : usize = 1000;

#[derive(rustyline_derive::Helper)]
struct ReplHelper {
    completer: FilenameCompleter,
    highlighter: MatchingBracketHighlighter,
    validator: MatchingBracketValidator,
    hinter: HistoryHinter,
    colored_prompt: String,
}

impl Completer for ReplHelper {
    type Candidate = Pair;

    fn complete(&self, line: &str, pos: usize, ctx: &Context<'_>)
        -> Result<(usize, Vec<Pair>), ReadlineError>
    {
        self.completer.complete(line, pos, ctx)
    }
}

impl Hinter for ReplHelper {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl Highlighter for ReplHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(&'s self, prompt: &'p str, default: bool)
        -> Cow<'b, str> /* Moo */
    {
        if default {
            Borrowed(&self.colored_prompt)
        } else {
            Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Owned(hint.blue().to_string())
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut validate::ValidationContext)
        -> rustyline::Result<validate::ValidationResult>
    {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

#[derive(Debug, Error)]
pub enum ReplError {
    #[error("Invalid command {command:?}")]
    InvalidCommand {
        command : String
    },
    #[error("Expected file path with load command `load path/to/file`")]
    MissingFilePath,
}

fn print_preamble_text() {
    println!("Cedille {0} REPL", crate_version!());
    println!("Type `help` to list available commands")
}

fn print_help_text() {
    // TODO: Add help text for the available REPL commands
}

fn repl_inner<H:Helper>(db: &mut Database, rl : &mut Editor<H>) -> Result<bool, CedilleError> {
    let line = rl.readline("> ")
        .map_err(|e| CedilleError::External(Box::new(e)))?;
    rl.add_history_entry(line.as_str());
    let mut words = line.split_ascii_whitespace();

    match words.next() {
        Some(command) => match command {
            "q" | "quit" => Ok(false),
            "h" | "help" => { 
                print_help_text();
                Ok(true)
            },
            "l" | "load" => match words.next() {
                Some(path) => {
                    let path = Path::new(path);
                    if path.is_file() {
                        // let mut file = fs::File::open(path)?;
                        // let mut contents = String::new();
                        // file.read_to_string(&mut contents)?;
                        // let module = parser::parse(db, &contents);
                        // dbg!(module);
                        let module = db.load_module_from_path(path)?;
                        // let holes = db.holes_to_errors(module);
                        // println!("{}", holes);
                    } else {
                        db.load_dir(path)?;
                    }

                    Ok(true)
                },
                None => Err(CedilleError::Collection(vec![]))
            },
            "m" | "meta" | "metas" => match words.next() {
                Some(path) => {
                    let path = Path::new(path);
                    let sym = cedille2_lang::database::path_to_module_symbol(Path::new(""), path)?;
                    if let Some(module_data) = db.get_metas(sym) {
                        use cedille2_core::metavar::MetaState;
                        for (key, state) in module_data.iter() {
                            print!("{} = ", *key);
                            match state {
                                MetaState::Unsolved => println!("{}", "unsolved".yellow()),
                                MetaState::Frozen => println!("{}", "frozen".bright_blue()),
                                MetaState::Solved(v) => println!("{:?}", v),
                            }
                        }
                    }
                    Ok(true)
                },
                None => Err(CedilleError::Collection(vec![]))
            }
            command => {
                let command = command.to_string();
                Err(CedilleError::Collection(vec![]))
            }
        },
        None => Ok(true)
    }
}

pub fn repl() {
    let mut db = Database::new();
    print_preamble_text();

    let config = Config::builder()
        .history_ignore_space(true)
        .completion_type(CompletionType::List)
        .output_stream(OutputStreamType::Stdout)
        .build();

    let helper = ReplHelper {
        completer: FilenameCompleter::new(),
        highlighter: MatchingBracketHighlighter::new(),
        hinter: HistoryHinter {},
        colored_prompt: "> ".green().to_string(),
        validator: MatchingBracketValidator::new(),
    };

    let mut rl = Editor::with_config(config);
    rl.set_helper(Some(helper));
    rl.bind_sequence(KeyEvent::new('\t', Modifiers::NONE), Cmd::Complete);
    rl.bind_sequence(KeyEvent::new(24 as char, Modifiers::NONE), Cmd::HistorySearchBackward);
    rl.bind_sequence(KeyEvent::new(25 as char, Modifiers::NONE), Cmd::HistorySearchForward);

    let proj_dirs = ProjectDirs::from("", "The University of Iowa", "Cedille");

    if let Some(proj_dirs) = &proj_dirs {
        let path = proj_dirs.data_local_dir();
        let path = path.join("repl_history.txt");
        rl.load_history(path.as_path()).ok();
        rl.history_mut().set_max_len(REPL_HISTORY_LIMIT);
    }

    loop {
        match repl_inner(&mut db, &mut rl) {
            Ok(r#continue) => if !r#continue { break; }
            Err(error) => {
                println!("{}", error)
            }
        }
    }

    if let Some(proj_dirs) = &proj_dirs {
        let path = proj_dirs.data_local_dir();
        fs::create_dir_all(&path).ok();
        let path = path.join("repl_history.txt");
        rl.save_history(&path).ok();
    }
}
