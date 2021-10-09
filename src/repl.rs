
use std::io;
use std::io::prelude::*;
use std::fs::File;

use anyhow::Result;
use thiserror::Error;

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
    println!("Cedille 2.0 REPL");
    println!("Type `help` to list available commands")
}

fn print_help_text() {
    // TODO: Add help text for the available REPL commands
}

fn repl_inner() -> Result<bool> {
    print!("> ");
    io::stdout().flush()?;

    let mut input = String::new();
    io::stdin().read_line(&mut input)?;
    let mut words = input.split_ascii_whitespace();

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
                    let _text = String::from_utf8(buffer)?;
                    // TODO: Parse and check text
                    Ok(true)
                },
                None => Err(ReplError::MissingFilePath.into())
            },
            command => {
                let command = command.to_string();
                let error = ReplError::InvalidCommand { command };
                Err(error.into())
            }
        },
        // If the user hits enter on accident with no text entered then ignore it
        None => Ok(true)
    }
}

pub fn repl() {
    print_preamble_text();
    loop {
        match repl_inner() {
            Ok(r#continue) => {
                if !r#continue { break; }
            },
            Err(error) => {
                // TODO: Improve error reporting, for now print the debug info
                println!("{:?}", error);
            }
        }
    }
}
