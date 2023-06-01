use std::io::{stdin, stdout, BufRead, Write};

use crate::lexer::{Lexer, Token};

pub fn start() {
    print!(">> ");
    stdout().flush().unwrap();
    let stdin = stdin();
    for line in stdin.lock().lines() {
        let mut l = Lexer::new(line.unwrap());
        loop {
            let t = l.next_token().unwrap();
            println!("{t:?}");
            if t == Token::Eof {
                break;
            }
        }
        print!("\n>> ");
        stdout().flush().unwrap();
    }
}
