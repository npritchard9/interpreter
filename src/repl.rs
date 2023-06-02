use std::io::{stdin, stdout, BufRead, Write};

use crate::{lexer::Lexer, parser::Parser};

pub fn start() {
    print!(">> ");
    stdout().flush().unwrap();
    let stdin = stdin();
    for line in stdin.lock().lines() {
        let l = Lexer::new(line.unwrap());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        if let Some(prog) = program {
            let errors = p.errors();
            if !errors.is_empty() {
                for e in errors {
                    println!("{e}");
                }
            }
            println!("{}", prog.to_string());
            print!("\n>> ");
            stdout().flush().unwrap();
        }
    }
}
