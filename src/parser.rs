use std::process;

use crate::lexer::{Lexer, Token};

#[derive(Debug)]
struct Parser {
    l: Lexer,
    cur_token: Token,
    peek_token: Token,
    errors: Vec<String>,
}

impl Parser {
    fn new(l: Lexer) -> Self {
        let mut p = Parser {
            l,
            cur_token: Token::Eof,
            peek_token: Token::Eof,
            errors: Vec::new(),
        };
        p.next_token();
        p.next_token();
        p
    }

    fn errors(&self) -> Vec<String> {
        self.errors.clone()
    }

    fn peek_error(&mut self, t: Token) {
        let e = format!(
            "expected next token to be {}, got {} instead",
            t.to_string(),
            self.peek_token.to_string()
        );
        self.errors.push(e);
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.l.next_token().unwrap();
    }

    fn cur_token_is(&self, t: Token) -> bool {
        self.cur_token == t
    }

    fn peek_token_is(&self, t: Token) -> bool {
        self.peek_token == t
    }

    fn expect_peek(&mut self, t: Token) -> bool {
        if self.peek_token_is(t.clone()) {
            self.next_token();
            return true;
        } else {
            self.peek_error(t);
            return false;
        }
    }

    fn parse_let_statement(&mut self) -> Option<Statement> {
        let mut stmt = LetStatement::new(self.cur_token.clone(), Token::Eof);
        if !self.expect_peek(Token::Ident(self.peek_token.to_string())) {
            return None;
        }
        stmt.name = Expression::new(self.cur_token.clone());
        if !self.expect_peek(Token::Assign) {
            return None;
        }
        while !self.cur_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Let(stmt))
    }

    fn parse_statement(&mut self) -> Option<Statement> {
        match self.cur_token {
            Token::Let => self.parse_let_statement(),
            _ => None,
        }
    }

    fn parse_program(&mut self) -> Option<Program> {
        let mut program = Program::new();
        while self.cur_token != Token::Eof {
            let stmt = self.parse_statement();
            if let Some(s) = stmt {
                program.statements.push(s);
            }
            self.next_token();
        }
        if program.statements.is_empty() {
            return None;
        } else {
            return Some(program);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Statement {
    Let(LetStatement),
    If(Token),
    Return(Token),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Expression {
    node: Token,
}

impl Expression {
    fn new(token: Token) -> Self {
        Expression { node: token }
    }
}

enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LetStatement {
    token: Token,
    name: Expression,
}

impl LetStatement {
    fn new(token: Token, name: Token) -> Self {
        LetStatement {
            token,
            name: Expression::new(name),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Program {
    statements: Vec<Statement>,
}

impl Program {
    fn new() -> Self {
        Program { statements: vec![] }
    }
    fn token_literal(&self) -> String {
        if self.statements.is_empty() {
            return "".into();
        } else {
            match self.statements[0].clone() {
                Statement::Let(l) => l.token.to_string(),
                Statement::If(i) => i.to_string(),
                Statement::Return(r) => r.to_string(),
            }
        }
    }
}

fn check_parser_errors(p: Parser) -> bool {
    if p.errors.is_empty() {
        return false;
    }
    println!("Parser has {} errors", p.errors.len());
    for e in p.errors {
        eprintln!("parser error: {e}")
    }
    true
}

pub fn test_let_statements() {
    // let input = r#"let x = 5;
    //         let y = 10;
    //         let foobar = 838383;"#;
    let input = r#"let x 5;
            let = 10;
            let 838383;"#;
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = check_parser_errors(p);
    if errors {
        process::exit(1);
    }
    assert_ne!(program, None, "the program should not be none");
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            3,
            "the program should have 3 statements"
        );
        let tests = vec!["x", "y", "foobar"];
        for (i, test) in tests.iter().enumerate() {
            let stmt = prog.statements[i].clone();
            if !test_let_statement(stmt, test.to_string()) {
                return;
            }
        }
    }
    println!("Passed");
}

fn test_let_statement(s: Statement, name: String) -> bool {
    match s {
        Statement::Let(l) => {
            if l.name.node.to_string() != name {
                return false;
            } else {
                return true;
            };
        }
        _ => false,
    }
}
