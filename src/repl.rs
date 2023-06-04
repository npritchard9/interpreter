use std::io::{stdin, stdout, BufRead, Write};

use crate::{
    environment::Environment,
    eval::eval,
    lexer::Lexer,
    object,
    parser::{Node, Parser},
};

pub fn start() {
    let mut env = Environment::new();
    print!(">> ");
    stdout().flush().unwrap();
    let stdin = stdin();
    for line in stdin.lock().lines() {
        let l = Lexer::new(line.unwrap());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        if let Some(prog) = program {
            let e = eval(Node::Prog(prog.clone()), &mut env);
            // let errors = p.errors();
            // if !errors.is_empty() {
            //     for e in errors {
            //         println!("{e}");
            //     }
            // }
            // let e = eval(Node::Prog(prog), env.clone());
            match e {
                object::Object::Int(i) => println!("{}", i.value),
                object::Object::Bool(b) => println!("{}", b.value),
                object::Object::Null => continue,
                object::Object::Return(_) => todo!(),
                object::Object::Error(e) => println!("{}", e.to_string()),
            }
            print!("\n>> ");
            stdout().flush().unwrap();
        }
    }
}
