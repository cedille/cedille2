
use std::io::prelude::*;
use std::fs::File;
use std::borrow::Cow::{self, Borrowed, Owned};

use anyhow::Result;
use thiserror::Error;
use clap::crate_version;
use colored::*;

use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::config::OutputStreamType;
use rustyline::error::ReadlineError;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{Cmd, CompletionType, Config, Context, Editor, Helper, KeyEvent, Modifiers};

use crate::syntax;

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
        -> Cow<'b, str>
    {
        if default {
            Borrowed(&self.colored_prompt)
        } else {
            Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        /* Owned("\x1b[1m".to_owned() + hint + "\x1b[m") */
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
enum ReplError {
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

fn repl_inner<H:Helper>(rl : &mut Editor<H>) -> Result<bool> {
    let line = rl.readline("> ")?;
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
                    let mut file = File::open(path)?;
                    let mut buffer = Vec::new();
                    file.read_to_end(&mut buffer)?;
                    let text = String::from_utf8(buffer)?;
                    /* let _parse = syntax::parse(text.as_str())?; */
                    // TODO: Parse and check text
                    Ok(true)
                },
                None => Err(ReplError::MissingFilePath.into())
            },
            command => {
                let command = command.to_string();
                Err(ReplError::InvalidCommand { command }.into())
            }
        },
        None => Ok(true)
    }
}

pub fn repl() {
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
/*         colored_prompt: format!("\x1b[1;32m{}\x1b[0m", "> "), */
        colored_prompt: "> ".green().to_string(),
        validator: MatchingBracketValidator::new(),
    };
    let mut rl = Editor::with_config(config);
    rl.set_helper(Some(helper));
    rl.bind_sequence(KeyEvent::new('\t', Modifiers::NONE), Cmd::Complete);
    rl.bind_sequence(KeyEvent::new(24 as char, Modifiers::NONE), Cmd::HistorySearchBackward);
    rl.bind_sequence(KeyEvent::new(25 as char, Modifiers::NONE), Cmd::HistorySearchForward);
    // If history fails to load we silently accept it
    rl.load_history("history.txt").ok();
    loop {
        match repl_inner(&mut rl) {
            Ok(r#continue) => if !r#continue { break; }
            Err(error) => {
                println!("{:?}", error)
            }
        }
    }
}
