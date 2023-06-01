use std::{collections::HashMap, process};

use crate::lexer::{Lexer, Token};

struct Parser {
    l: Lexer,
    cur_token: Token,
    peek_token: Token,
    errors: Vec<String>,
    prefix_parse_fns: HashMap<usize, PrefixParseFn>,
    infix_parse_fns: HashMap<usize, InfixParseFn>,
}

impl Parser {
    fn new(l: Lexer) -> Self {
        let mut p = Parser {
            l,
            cur_token: Token::Eof,
            peek_token: Token::Eof,
            errors: Vec::new(),
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
        };
        p.register_prefix(
            Token::Ident("".to_string()).into(),
            Parser::parse_identifier,
        );
        p.register_prefix(
            Token::Int("0".to_string()).into(),
            Parser::parse_integer_literal,
        );
        p.next_token();
        p.next_token();
        p
    }

    fn check_errors(&self) -> bool {
        if self.errors.is_empty() {
            return false;
        }
        println!("Parser has {} errors", self.errors.len());
        for e in self.errors.iter() {
            eprintln!("parser error: {e}")
        }
        true
    }

    fn peek_error(&mut self, t: Token) {
        let e = format!(
            "expected next token to be {}, got {} instead",
            t.to_string(),
            self.peek_token.to_string()
        );
        self.errors.push(e);
    }

    fn get_token_index(t: &Token) -> usize {
        unsafe { *(t as *const Token as *const usize) }
    }

    fn register_prefix(&mut self, t: Token, f: PrefixParseFn) {
        self.prefix_parse_fns.insert(Parser::get_token_index(&t), f);
    }

    fn register_infix(&mut self, t: Token, f: InfixParseFn) {
        self.infix_parse_fns.insert(Parser::get_token_index(&t), f);
    }

    fn parse_identifier(&self) -> Expression {
        Expression::new(self.cur_token.clone())
    }

    // not sure about the return
    fn parse_integer_literal(&self) -> Expression {
        Expression::new(self.cur_token.clone())
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
        let mut stmt = LetStatement::new(
            self.cur_token.clone(),
            self.peek_token.clone(),
            self.peek_token.clone(),
        );
        if !self.expect_peek(Token::Ident(self.peek_token.to_string())) {
            return None;
        }
        stmt.name = self.cur_token.clone();
        if !self.expect_peek(Token::Assign) {
            return None;
        }
        while !self.cur_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Let(stmt))
    }

    fn parse_return_statement(&mut self) -> Option<Statement> {
        let stmt = ReturnStatement::new(self.cur_token.clone(), self.peek_token.clone());
        self.next_token();

        while !self.cur_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Return(stmt))
    }

    fn parse_expression_statement(&mut self) -> Option<Statement> {
        let mut stmt = ExpressionStatement::new(self.cur_token.clone());
        stmt.expression = self.parse_expression(Prio::Lowest as usize).unwrap();
        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Expression(stmt))
    }

    fn parse_expression(&self, prio: usize) -> Option<Expression> {
        let prefix = self
            .prefix_parse_fns
            .get(&Parser::get_token_index(&self.cur_token));
        if let Some(p) = prefix {
            let left_exp = p(self);
            return Some(left_exp);
        } else {
            return None;
        }
    }

    fn parse_statement(&mut self) -> Option<Statement> {
        match self.cur_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
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
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl ToString for Statement {
    fn to_string(&self) -> String {
        match self {
            Statement::Let(l) => l.to_string(),
            Statement::If(i) => i.to_string(),
            Statement::Return(r) => r.to_string(),
            Statement::Expression(e) => todo!(),
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpressionStatement {
    token: Token,
    expression: Expression,
}

impl ExpressionStatement {
    fn new(token: Token) -> Self {
        ExpressionStatement {
            token: token.clone(),
            expression: Expression::new(token.clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IntegerLiteral {
    token: Token,
    value: isize,
}

impl IntegerLiteral {
    fn new(token: Token) -> Self {
        let Token::Int(i) = token.clone() else {panic!("This is not an integer")};
        IntegerLiteral {
            token,
            value: i.parse::<isize>().unwrap(),
        }
    }
}

enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LetStatement {
    token: Token,
    name: Token,
    value: Token,
}

impl LetStatement {
    fn new(token: Token, name: Token, value: Token) -> Self {
        LetStatement { token, name, value }
    }
}

impl ToString for LetStatement {
    fn to_string(&self) -> String {
        format!(
            "{} {} = {};",
            self.token.to_string(),
            self.name.to_string(),
            self.value.to_string()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReturnStatement {
    token: Token,
    value: Token,
}

impl ReturnStatement {
    fn new(token: Token, value: Token) -> Self {
        ReturnStatement { token, value }
    }
}

impl ToString for ReturnStatement {
    fn to_string(&self) -> String {
        format!("{} {};", self.token.to_string(), self.value.to_string(),)
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
}

impl ToString for Program {
    fn to_string(&self) -> String {
        let mut s = String::new();
        for stmt in self.statements.iter() {
            s.push_str(stmt.to_string().as_str());
        }
        s
    }
}

type PrefixParseFn = fn(&Parser) -> Expression;
type InfixParseFn = fn(&Parser, Expression) -> Expression;

enum Prio {
    Lowest = 1,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

pub fn test_let_statements() {
    let input = r#"let x = 5;
            let y = 10;
            let foobar = 838383;"#;
    // let input = r#"let x 5;
    //         let = 10;
    //         let 838383;"#;
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    assert_ne!(program, None, "the program should not be none");
    if let Some(prog) = program {
        println!("prog stmts: {:?}", prog.statements);
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
    println!("Passed test let statements");
}

fn test_let_statement(s: Statement, name: String) -> bool {
    match s {
        Statement::Let(l) => {
            if l.name.to_string() != name {
                return false;
            } else {
                return true;
            };
        }
        _ => false,
    }
}

pub fn test_return_statements() {
    let input = r#"return 5;
            return 10;
            return 993322;"#;
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
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
        for s in prog.statements.iter() {
            match s {
                Statement::Return(r) => {
                    if r.token.to_string() != "return" {
                        println!("return literal not return, got {}", r.value.to_string())
                    }
                }
                _ => println!("statement is not a return, got {s:?}"),
            }
        }
    }
    println!("Passed test return statements");
}

pub fn test_string() {
    let mut program = Program::new();
    let statements = vec![Statement::Let(LetStatement::new(
        Token::Let,
        Token::Ident("myVar".to_string()),
        Token::Ident("anotherVar".to_string()),
    ))];
    program.statements = statements;
    assert_eq!(
        program.to_string(),
        "let myVar = anotherVar;",
        "program string wrong, got {}",
        program.to_string()
    );
    println!("Passed test string");
}

pub fn test_identifier_expression() {
    let input = "foobar;";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    println!("prog: {program:?}");
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program has not enough statements. got {}",
            prog.statements.len()
        );
        match prog.statements[0].clone() {
            Statement::Expression(e) => match e.token {
                Token::Ident(i) => {
                    assert_eq!(i, "foobar", "ident value not foobar, got {i}")
                }
                _ => println!("token is not an identifier, got {:?}", e.token),
            },
            _ => println!(
                "Statement is not an expression, got {:?}",
                prog.statements[0].clone()
            ),
        }
    }
    println!("Passed test identifier expression");
}

pub fn test_integer_literal_expression() {
    let input = "5;";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    println!("prog: {program:?}");
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program has not enough statements. got {}",
            prog.statements.len()
        );
        match prog.statements[0].clone() {
            Statement::Expression(e) => match e.token {
                Token::Int(i) => {
                    assert_eq!(i.parse::<isize>().unwrap(), 5, "ident value not 5, got {i}");
                    assert_eq!(i, "5", "ident literal not '5', got {i}")
                }
                _ => println!("token is not an identifier, got {:?}", e.token),
            },
            _ => println!(
                "Statement is not an expression, got {:?}",
                prog.statements[0].clone()
            ),
        }
    }
    println!("Passed test integer literal expression");
}
