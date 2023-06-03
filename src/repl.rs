use std::io::{stdin, stdout, BufRead, Write};

use crate::{
    eval::eval,
    lexer::Lexer,
    parser::{Node, Parser},
};

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
            let e = eval(Node::Prog(prog));
            match e {
                crate::object::Object::Int(i) => println!("{}", i.value),
                crate::object::Object::Bool(b) => println!("{}", b.value),
                crate::object::Object::Null => todo!(),
                crate::object::Object::Return(_) => todo!(),
            }
            print!("\n>> ");
            stdout().flush().unwrap();
        }
    }
}
