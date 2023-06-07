use std::{collections::HashMap, process};

use crate::lexer::{Lexer, Token};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Expr(Expression),
    Stmt(Statement),
    Prog(Program),
}

pub struct Parser {
    l: Lexer,
    cur_token: Token,
    peek_token: Token,
    errors: Vec<String>,
    prefix_parse_fns: HashMap<usize, PrefixParseFn>,
    infix_parse_fns: HashMap<usize, InfixParseFn>,
}

impl Parser {
    pub fn new(l: Lexer) -> Self {
        let mut p = Parser {
            l,
            cur_token: Token::Eof,
            peek_token: Token::Eof,
            errors: Vec::new(),
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
        };
        p.next_token();
        p.next_token();
        p.register_prefix(
            Token::Ident("".to_string()),
            PrefixParseFn::Ref(Parser::parse_identifier),
        );
        p.register_prefix(
            Token::Int("0".to_string()),
            PrefixParseFn::Ref(Parser::parse_integer_literal),
        );
        p.register_prefix(
            Token::Bang,
            PrefixParseFn::Mut(Parser::parse_prefix_expression),
        );
        p.register_prefix(
            Token::Minus,
            PrefixParseFn::Mut(Parser::parse_prefix_expression),
        );
        p.register_prefix(
            Token::True,
            PrefixParseFn::Ref(Parser::parse_boolean_literal),
        );
        p.register_prefix(
            Token::False,
            PrefixParseFn::Ref(Parser::parse_boolean_literal),
        );
        p.register_prefix(
            Token::Lparen,
            PrefixParseFn::Mut(Parser::parse_grouped_expression),
        );
        p.register_prefix(Token::If, PrefixParseFn::Mut(Parser::parse_if_expression));
        p.register_prefix(
            Token::Function,
            PrefixParseFn::Mut(Parser::parse_fn_literal),
        );
        p.register_prefix(
            Token::TString("".to_string()),
            PrefixParseFn::Ref(Parser::parse_string_literal),
        );
        p.register_prefix(
            Token::Lbracket,
            PrefixParseFn::Mut(Parser::parse_array_literal),
        );
        p.register_infix(Token::Plus, Parser::parse_infix_expression);
        p.register_infix(Token::Minus, Parser::parse_infix_expression);
        p.register_infix(Token::Slash, Parser::parse_infix_expression);
        p.register_infix(Token::Asterisk, Parser::parse_infix_expression);
        p.register_infix(Token::Equal, Parser::parse_infix_expression);
        p.register_infix(Token::NotEqual, Parser::parse_infix_expression);
        p.register_infix(Token::LessThan, Parser::parse_infix_expression);
        p.register_infix(Token::GreaterThan, Parser::parse_infix_expression);
        p.register_infix(Token::Lparen, Parser::parse_call_expression);
        p
    }

    pub fn errors(&self) -> Vec<String> {
        self.errors.clone()
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

    fn peek_precedence(&self) -> usize {
        match self.peek_token {
            Token::Equal | Token::NotEqual => Prio::Equals as usize,
            Token::LessThan | Token::GreaterThan => Prio::LessGreater as usize,
            Token::Plus | Token::Minus => Prio::Sum as usize,
            Token::Slash | Token::Asterisk => Prio::Product as usize,
            Token::Lparen => Prio::Call as usize,
            _ => Prio::Lowest as usize,
        }
    }

    fn cur_precedence(&self) -> usize {
        match self.cur_token {
            Token::Equal | Token::NotEqual => Prio::Equals as usize,
            Token::LessThan | Token::GreaterThan => Prio::LessGreater as usize,
            Token::Plus | Token::Minus => Prio::Sum as usize,
            Token::Slash | Token::Asterisk => Prio::Product as usize,
            Token::Lparen => Prio::Call as usize,
            _ => Prio::Lowest as usize,
        }
    }

    fn no_prefix_parse_fn_error(&mut self, t: Token) {
        let msg = format!("no prefix parse function for {} found", t.to_string());
        self.errors.push(msg);
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
        Expression::Id(self.cur_token.clone())
    }

    fn parse_expression_list(&mut self, end: Token) -> Vec<Option<Box<Expression>>> {
        let mut list = vec![];
        if self.peek_token_is(end.clone()) {
            self.next_token();
            return list;
        }
        self.next_token();
        list.push(self.parse_expression(Prio::Lowest as usize));
        while self.peek_token_is(Token::Comma) {
            self.next_token();
            self.next_token();
            list.push(self.parse_expression(Prio::Lowest as usize));
        }
        if !self.expect_peek(end) {
            return list;
        }
        list
    }

    fn parse_array_literal(&mut self) -> Expression {
        let mut array = ArrayLiteral::new(self.cur_token.clone());
        array.elements = self.parse_expression_list(Token::Rbracket);
        Expression::ArrayLit(array)
    }

    fn parse_string_literal(&self) -> Expression {
        Expression::StringLit(StringLiteral::new(self.cur_token.clone()))
    }

    fn parse_integer_literal(&self) -> Expression {
        Expression::IntLit(IntegerLiteral::new(self.cur_token.clone()))
    }

    fn parse_boolean_literal(&self) -> Expression {
        Expression::BoolLit(BooleanLiteral::new(self.cur_token.clone()))
    }

    fn parse_grouped_expression(&mut self) -> Expression {
        self.next_token();
        let expr = self.parse_expression(Prio::Lowest as usize);
        if !self.expect_peek(Token::Rparen) {
            return *expr.unwrap();
        }
        *expr.unwrap()
    }

    fn parse_fn_literal(&mut self) -> Expression {
        let mut func = FunctionLiteral::new(self.cur_token.clone());
        if !self.expect_peek(Token::Lparen) {
            return Expression::Fn(func);
        }
        func.params = self.parse_fn_params();
        if !self.expect_peek(Token::Lbrace) {
            return Expression::Fn(func);
        }
        func.body = self.parse_block_statement();
        Expression::Fn(func)
    }

    fn parse_fn_params(&mut self) -> Vec<Token> {
        let mut tokens = vec![];
        if self.peek_token_is(Token::Rparen) {
            self.next_token();
            return tokens;
        }
        self.next_token();
        tokens.push(self.cur_token.clone());
        while self.peek_token_is(Token::Comma) {
            self.next_token();
            self.next_token();
            tokens.push(self.cur_token.clone());
        }
        if !self.expect_peek(Token::Rparen) {
            return tokens;
        }
        tokens
    }

    fn parse_call_expression(&mut self, func: Expression) -> Expression {
        let mut expr = CallExpression::new(self.cur_token.clone(), func);
        // expr.args = self.parse_call_arguments();
        expr.args = self.parse_expression_list(Token::Rparen);
        Expression::Call(expr)
    }

    fn parse_call_arguments(&mut self) -> Vec<Option<Box<Expression>>> {
        let mut args = vec![];
        if self.peek_token_is(Token::Rparen) {
            self.next_token();
            return args;
        }
        self.next_token();
        args.push(self.parse_expression(Prio::Lowest as usize));
        while self.peek_token_is(Token::Comma) {
            self.next_token();
            self.next_token();
            args.push(self.parse_expression(Prio::Lowest as usize));
        }

        if !self.expect_peek(Token::Rparen) {
            return args;
        }
        args
    }

    fn parse_if_expression(&mut self) -> Expression {
        let mut expr = If::new(
            self.cur_token.clone(),
            None,
            BlockStatement::new(self.cur_token.clone()),
            None,
        );
        if !self.expect_peek(Token::Lparen) {
            return Expression::If(expr);
        }
        self.next_token();
        expr.cond = self.parse_expression(Prio::Lowest as usize);
        if !self.expect_peek(Token::Rparen) {
            return Expression::If(expr);
        }
        if !self.expect_peek(Token::Lbrace) {
            return Expression::If(expr);
        }
        expr.consequence = self.parse_block_statement();
        if self.peek_token_is(Token::Else) {
            self.next_token();
            if !self.expect_peek(Token::Lbrace) {
                return Expression::If(expr);
            }
            expr.alternative = Some(self.parse_block_statement());
        }
        Expression::If(expr)
    }

    fn parse_block_statement(&mut self) -> BlockStatement {
        let mut block = BlockStatement::new(self.cur_token.clone());
        self.next_token();
        while !self.cur_token_is(Token::Rbrace) && !self.cur_token_is(Token::Eof) {
            let stmt = self.parse_statement();
            if let Some(s) = stmt {
                block.statements.push(s);
            }
            self.next_token();
        }
        block
    }

    fn parse_prefix_expression(&mut self) -> Expression {
        let mut expr = PrefixExpression::new(self.cur_token.clone(), self.cur_token.to_string());
        self.next_token();
        expr.right = self.parse_expression(Prio::Prefix as usize);
        Expression::Prefix(expr)
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Expression {
        let mut expr =
            InfixExpression::new(self.cur_token.clone(), left, self.cur_token.to_string());
        let prec = self.cur_precedence();
        self.next_token();
        expr.right = Some(self.parse_expression(prec).unwrap());
        Expression::Infix(expr)
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
            true
        } else {
            self.peek_error(t);
            false
        }
    }

    fn parse_let_statement(&mut self) -> Option<Statement> {
        let mut stmt = LetStatement::new(self.cur_token.clone(), self.peek_token.clone());
        if !self.expect_peek(Token::Ident(self.peek_token.to_string())) {
            return None;
        }
        stmt.name = self.cur_token.clone();
        if !self.expect_peek(Token::Assign) {
            return None;
        }
        self.next_token();
        stmt.value = self.parse_expression(Prio::Lowest as usize);
        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Let(stmt))
    }

    fn parse_return_statement(&mut self) -> Option<Statement> {
        let mut stmt = ReturnStatement::new(self.cur_token.clone());
        self.next_token();

        stmt.value = self.parse_expression(Prio::Lowest as usize);

        while !self.cur_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Return(stmt))
    }

    fn parse_expression_statement(&mut self) -> Option<Statement> {
        let mut stmt = ExpressionStatement::new(self.cur_token.clone());
        stmt.expression = self.parse_expression(Prio::Lowest as usize);
        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        }
        Some(Statement::Expression(stmt))
    }

    fn parse_expression(&mut self, prec: usize) -> Option<Box<Expression>> {
        let prefix = self
            .prefix_parse_fns
            .get(&Parser::get_token_index(&self.cur_token));
        if let Some(p) = prefix {
            let mut left_exp = match p {
                PrefixParseFn::Ref(pr) => pr(self),
                PrefixParseFn::Mut(pm) => pm(self),
            };
            while !self.peek_token_is(Token::Semicolon) && prec < self.peek_precedence() {
                let infix_exists = self
                    .infix_parse_fns
                    .contains_key(&Parser::get_token_index(&self.peek_token.clone()));
                if !infix_exists {
                    return Some(Box::new(left_exp));
                }
                let infix =
                    self.infix_parse_fns[&Parser::get_token_index(&self.peek_token.clone())];
                self.next_token();
                left_exp = infix(self, left_exp);
            }
            Some(Box::new(left_exp))
        } else {
            self.no_prefix_parse_fn_error(self.cur_token.clone());
            None
        }
    }

    fn parse_statement(&mut self) -> Option<Statement> {
        match self.cur_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    pub fn parse_program(&mut self) -> Option<Program> {
        let mut program = Program::new();
        while self.cur_token != Token::Eof {
            let stmt = self.parse_statement();
            if let Some(s) = stmt {
                program.statements.push(s);
            }
            self.next_token();
        }
        if program.statements.is_empty() {
            None
        } else {
            Some(program)
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
    Block(BlockStatement),
}

impl ToString for Statement {
    fn to_string(&self) -> String {
        match self {
            Statement::Let(l) => l.to_string(),
            Statement::Return(r) => r.to_string(),
            Statement::Expression(e) => match e.expression.clone() {
                Some(se) => match *se {
                    Expression::Prefix(pe) => pe.to_string(),
                    Expression::Infix(ie) => ie.to_string(),
                    Expression::IntLit(ile) => ile.token.to_string(),
                    Expression::BoolLit(ble) => ble.token.to_string(),
                    Expression::StringLit(sle) => sle.token.to_string(),
                    Expression::ArrayLit(ale) => ale.to_string(),
                    Expression::If(ife) => ife.to_string(),
                    Expression::Id(ide) => ide.to_string(),
                    Expression::Fn(fe) => fe.to_string(),
                    Expression::Call(ce) => ce.to_string(),
                },
                None => String::from(""),
            },
            Statement::Block(b) => b.to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    IntLit(IntegerLiteral),
    BoolLit(BooleanLiteral),
    StringLit(StringLiteral),
    ArrayLit(ArrayLiteral),
    If(If),
    Id(Token),
    Fn(FunctionLiteral),
    Call(CallExpression),
}

impl ToString for Expression {
    fn to_string(&self) -> String {
        match self {
            Expression::Prefix(pe) => pe.to_string(),
            Expression::Infix(ie) => ie.to_string(),
            Expression::IntLit(ile) => ile.token.to_string(),
            Expression::BoolLit(ble) => ble.token.to_string(),
            Expression::StringLit(sle) => sle.token.to_string(),
            Expression::ArrayLit(ale) => ale.to_string(),
            Expression::If(ife) => ife.to_string(),
            Expression::Id(ide) => ide.to_string(),
            Expression::Fn(fe) => fe.to_string(),
            Expression::Call(ce) => ce.to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Option<Box<Expression>>,
}

impl ExpressionStatement {
    fn new(token: Token) -> Self {
        ExpressionStatement {
            token,
            expression: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteral {
    pub token: Token,
    pub value: String,
}

impl StringLiteral {
    fn new(token: Token) -> Self {
        let Token::TString(s) = token.clone() else {panic!("This is not a string")};
        StringLiteral {
            token,
            value: s.parse().unwrap(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: isize,
}

impl IntegerLiteral {
    fn new(token: Token) -> Self {
        let Token::Int(i) = token.clone() else {panic!("This is not an integer")};
        IntegerLiteral {
            token,
            value: i.parse().unwrap(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BooleanLiteral {
    pub token: Token,
    pub value: bool,
}

impl BooleanLiteral {
    fn new(token: Token) -> Self {
        BooleanLiteral {
            token: token.clone(),
            value: token.to_string().parse().unwrap(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayLiteral {
    pub token: Token,
    pub elements: Vec<Option<Box<Expression>>>,
}

impl ArrayLiteral {
    pub fn new(token: Token) -> Self {
        ArrayLiteral {
            token,
            elements: vec![],
        }
    }
}

impl ToString for ArrayLiteral {
    fn to_string(&self) -> String {
        let mut els = vec![];
        for e in self.elements.iter() {
            els.push(e.clone().unwrap().to_string())
        }
        format!("[{}]", els.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct If {
    pub token: Token,
    pub cond: Option<Box<Expression>>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl If {
    fn new(
        token: Token,
        cond: Option<Box<Expression>>,
        consequence: BlockStatement,
        alternative: Option<BlockStatement>,
    ) -> Self {
        If {
            token,
            cond,
            consequence,
            alternative,
        }
    }
}

impl ToString for If {
    fn to_string(&self) -> String {
        let cond = match self.cond.clone() {
            Some(c) => c.to_string(),
            None => "".to_string(),
        };
        let mut if_expr = format!("if {cond} {}", self.consequence.to_string());
        if let Some(alt) = self.alternative.clone() {
            let alt_expr = format!(" else {}", alt.to_string());
            if_expr.push_str(alt_expr.as_str());
        }
        if_expr
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionLiteral {
    pub token: Token,
    pub params: Vec<Token>,
    pub body: BlockStatement,
}

impl FunctionLiteral {
    fn new(token: Token) -> Self {
        FunctionLiteral {
            token: token.clone(),
            params: Vec::new(),
            body: BlockStatement::new(token),
        }
    }
}

impl ToString for FunctionLiteral {
    fn to_string(&self) -> String {
        let mut params: Vec<String> = vec![];
        for p in self.params.iter() {
            params.push(p.to_string());
        }
        format!(
            "{}({}) {}",
            self.token.to_string(),
            params.join(", "),
            self.body.to_string()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpression {
    pub token: Token,
    pub func: Box<Expression>,
    pub args: Vec<Option<Box<Expression>>>,
}

impl CallExpression {
    fn new(token: Token, func: Expression) -> Self {
        CallExpression {
            token,
            func: Box::new(func),
            args: Vec::new(),
        }
    }
}

impl ToString for CallExpression {
    fn to_string(&self) -> String {
        let mut args: Vec<String> = vec![];
        for a in self.args.iter() {
            args.push(a.clone().unwrap().to_string());
        }
        format!("{}({})", self.func.to_string(), args.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

impl BlockStatement {
    fn new(token: Token) -> Self {
        BlockStatement {
            token,
            statements: Vec::new(),
        }
    }
}

impl ToString for BlockStatement {
    fn to_string(&self) -> String {
        let mut stmts = String::new();
        for s in self.statements.iter() {
            stmts.push_str(s.to_string().as_str());
        }
        stmts
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStatement {
    pub token: Token,
    pub name: Token,
    pub value: Option<Box<Expression>>,
}

impl LetStatement {
    fn new(token: Token, name: Token) -> Self {
        LetStatement {
            token,
            name,
            value: None,
        }
    }

    fn new_full(token: Token, name: Token, value: Expression) -> Self {
        LetStatement {
            token,
            name,
            value: Some(Box::new(value)),
        }
    }
}

impl ToString for LetStatement {
    fn to_string(&self) -> String {
        format!(
            "{} {} = {};",
            self.token.to_string(),
            self.name.to_string(),
            self.value.clone().unwrap().to_string()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnStatement {
    pub token: Token,
    pub value: Option<Box<Expression>>,
}

impl ReturnStatement {
    fn new(token: Token) -> Self {
        ReturnStatement { token, value: None }
    }
}

impl ToString for ReturnStatement {
    fn to_string(&self) -> String {
        format!(
            "{} {};",
            self.token.to_string(),
            self.value.clone().unwrap().to_string(),
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
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

type PrefixParseFnRef = fn(&Parser) -> Expression;
type PrefixParseFnMut = fn(&mut Parser) -> Expression;
enum PrefixParseFn {
    Ref(PrefixParseFnRef),
    Mut(PrefixParseFnMut),
}
type InfixParseFn = fn(&mut Parser, Expression) -> Expression;

enum Prio {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrefixExpression {
    pub token: Token,
    pub op: String,
    pub right: Option<Box<Expression>>,
}

impl PrefixExpression {
    fn new(token: Token, op: String) -> Self {
        PrefixExpression {
            token,
            op,
            right: None,
        }
    }
}

impl ToString for PrefixExpression {
    fn to_string(&self) -> String {
        let right = match self.right.clone() {
            Some(expr) => match *expr {
                Expression::Prefix(p) => p.to_string(),
                Expression::Infix(i) => i.to_string(),
                Expression::IntLit(il) => il.token.to_string(),
                Expression::BoolLit(ble) => ble.token.to_string(),
                Expression::StringLit(sle) => sle.token.to_string(),
                Expression::ArrayLit(ale) => ale.to_string(),
                Expression::If(ife) => ife.to_string(),
                Expression::Id(id) => id.to_string(),
                Expression::Fn(fe) => fe.to_string(),
                Expression::Call(ce) => ce.to_string(),
            },
            None => "".to_string(),
        };
        format!("({}{})", self.op, right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Option<Box<Expression>>,
    pub op: String,
    pub right: Option<Box<Expression>>,
}

impl InfixExpression {
    fn new(token: Token, left: Expression, op: String) -> Self {
        InfixExpression {
            token,
            left: Some(Box::new(left)),
            op,
            right: None,
        }
    }
}

impl ToString for InfixExpression {
    fn to_string(&self) -> String {
        let left = match self.left.clone() {
            Some(l) => l.to_string(),
            None => "".to_string(),
        };
        let right = match self.right.clone() {
            Some(r) => r.to_string(),
            None => "".to_string(),
        };
        format!("({} {} {})", left, self.op, right)
    }
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
        Statement::Let(l) => l.name.to_string() == name,
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
                        println!(
                            "return literal not return, got {}",
                            r.value.clone().unwrap().to_string()
                        )
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
    let statements = vec![Statement::Let(LetStatement::new_full(
        Token::Let,
        Token::Ident("myVar".to_string()),
        Expression::Id(Token::Ident("anotherVar".to_string())),
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

pub fn test_boolean_literal_expression() {
    let input = "true;";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program has not enough statements. got {}",
            prog.statements.len()
        );
        match prog.statements[0].clone() {
            Statement::Expression(e) => match e.token {
                Token::True => {
                    let b: bool = e.token.to_string().parse().unwrap();
                    assert!(b, "bool value not true, got {b}");
                }
                _ => println!("token is not a bool, got {:?}", e.token),
            },
            _ => println!(
                "Statement is not an expression, got {:?}",
                prog.statements[0].clone()
            ),
        }
    }
    println!("Passed test boolean literal expression");
}

// add bool tests
pub fn test_prefix_expressions() {
    let prefix_tests = vec![("!5", "!", 5), ("-15", "-", 15)];
    for test in prefix_tests {
        let l = Lexer::new(test.0.to_string());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        let errors = p.check_errors();
        if errors {
            process::exit(1);
        }
        if let Some(prog) = program {
            assert_eq!(
                prog.statements.len(),
                1,
                "program has not enough statements. got {}",
                prog.statements.len()
            );
            match prog.statements[0].clone() {
                Statement::Expression(e) => match e.expression {
                    Some(se) => match *se {
                        Expression::Prefix(pe) => {
                            if !test_integer_literal(*pe.right.unwrap(), test.2) {
                                println!("integer literal test failed")
                            }
                        }
                        e => {
                            println!("stmt is not a prefix expression, got {:#?}", e)
                        }
                    },
                    None => todo!(),
                },
                _ => println!(
                    "Statement is not an expression, got {:?}",
                    prog.statements[0].clone()
                ),
            }
        }
    }
    println!("Passed test prefix expressions");
}

pub fn test_integer_literal(il: Expression, value: isize) -> bool {
    match il {
        Expression::Prefix(pe) => {
            let integ: isize = pe.token.to_string().parse().unwrap();
            if integ != value {
                println!("integ.value not {value}, got {}", integ);
                return false;
            }
        }
        Expression::Infix(ie) => {
            let integ: isize = ie.token.to_string().parse().unwrap();
            if integ != value {
                println!("integ.value not {value}, got {}", integ);
                return false;
            }
        }
        Expression::IntLit(ile) => {
            let integ: isize = ile.token.to_string().parse().unwrap();
            if integ != value {
                println!("integ.value not {value}, got {}", integ);
                return false;
            }
        }
        Expression::BoolLit(_) => panic!("can't have a bool holding an int"),
        // not sure
        Expression::If(_) => panic!("can't have an if holding an int"),
        Expression::Id(ide) => {
            let integ: isize = ide.to_string().parse().unwrap();
            if integ != value {
                println!("integ.value not {value}, got {}", integ);
                return false;
            }
        }
        Expression::Fn(_) => panic!("can't have a function holding an int"),
        Expression::Call(_) => panic!("can't have a call holding an int"),
        Expression::StringLit(_) => panic!("can't have a string holding an int"),
        Expression::ArrayLit(_) => panic!("can't have an array holding an int"),
    }
    true
}

// add bool tests
pub fn test_infix_expressions() {
    let ops = vec!["+", "-", "*", "/", ">", "<", "==", "!="];
    let mut infix_tests = vec![];
    for op in ops {
        infix_tests.push((format!("5 {} 5;", op), 5, op, 5));
    }

    for test in infix_tests {
        let l = Lexer::new(test.0.to_string());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        let errors = p.check_errors();
        if errors {
            process::exit(1);
        }
        if let Some(prog) = program {
            assert_eq!(
                prog.statements.len(),
                1,
                "program has not enough statements. got {}, with {:#?}",
                prog.statements.len(),
                prog.statements
            );
            match prog.statements[0].clone() {
                Statement::Expression(e) => match e.expression {
                    Some(se) => match *se {
                        Expression::Infix(ie) => {
                            let ans = test_integer_literal(*ie.left.unwrap(), test.1);
                            if !ans {
                                println!("literal wrong")
                            }
                            assert_eq!(ie.op, test.2, "Operator is not {}, got {}", ie.op, test.2);
                            let ans = test_integer_literal(*ie.right.unwrap(), test.3);
                            if !ans {
                                println!("literal wrong")
                            }
                        }
                        e => {
                            println!("stmt is not an infix expression, got {:?}", e);
                        }
                    },
                    None => todo!(),
                },
                _ => println!(
                    "Statement is not an expression, got {:?}",
                    prog.statements[0].clone()
                ),
            }
        }
    }
    println!("Passed test infix expressions")
}

pub fn test_operator_precedence_parsing() {
    let tests = vec![
        ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
        (
            "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
            "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
        ),
        (
            "add(a + b + c * d / f + g)",
            "add((((a + b) + ((c * d) / f)) + g))",
        ),
        ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
        ("(5 + 5) * 2", "((5 + 5) * 2)"),
        ("2 / (5 + 5)", "(2 / (5 + 5))"),
        ("-(5 + 5)", "(-(5 + 5))"),
        ("!(true == true)", "(!(true == true))"),
        ("true", "true"),
        ("false", "false"),
        ("3 > 5 == false", "((3 > 5) == false)"),
        ("3 < 5 == true", "((3 < 5) == true)"),
        ("-a * b", "((-a) * b)"),
        ("!-a", "(!(-a))"),
        ("a + b + c", "((a + b) + c)"),
        ("a + b - c", "((a + b) - c)"),
        ("a * b * c", "((a * b) * c)"),
        ("a * b / c", "((a * b) / c)"),
        ("a + b / c", "(a + (b / c))"),
        ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
        ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
        ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
        ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
        (
            "3 + 4 * 5 == 3 * 1 + 4 * 5",
            "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
        ),
        (
            "3 + 4 * 5 == 3 * 1 + 4 * 5",
            "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
        ),
    ];

    for test in tests {
        let l = Lexer::new(test.0.to_string());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        let errors = p.check_errors();
        if errors {
            process::exit(1);
        }
        if let Some(prog) = program {
            let actual = prog.to_string();
            assert_eq!(
                actual,
                test.1.to_string(),
                "expected {}, got {}",
                test.1,
                actual
            )
        }
    }
    println!("Passed test operator precedence parsing")
}

pub fn test_if_expression() {
    let input = "if (x < y) { x }";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program body does not contain 1 statement, got {}",
            prog.statements.len()
        );
        let s = prog.statements[0].clone();
        match s.clone() {
            Statement::Expression(e) => match *e.expression.unwrap() {
                Expression::If(ife) => {
                    // add test infix
                    assert_eq!(
                        ife.consequence.statements.len(),
                        1,
                        "consequence is not 1 stmt, got {}",
                        ife.consequence.statements.len()
                    );
                    match ife.consequence.statements[0].clone() {
                        Statement::Expression(exp) => {
                            assert_eq!(
                                exp.token.to_string(),
                                "x",
                                "did not get x, got {}",
                                exp.token.to_string()
                            )
                        }
                        _ => println!(
                            "statement[0] is not an expression, got {}",
                            ife.consequence.statements[0].to_string()
                        ),
                    }
                    if ife.alternative.is_some() {
                        println!(
                            "alternative was not null, got {:?}",
                            ife.alternative.unwrap()
                        )
                    }
                }
                _ => print!("expr is not an if, got {}", s.to_string()),
            },
            _ => println!("stmt is not an expression, got {}", s.to_string()),
        };
    }
    println!("Passed test if expressions");
}

pub fn test_if_else_expression() {
    let input = "if (x < y) { x } else { y }";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program body does not contain 1 statement, got {}",
            prog.statements.len()
        );
        let s = prog.statements[0].clone();

        match s.clone() {
            Statement::Expression(e) => match *e.expression.unwrap() {
                Expression::If(ife) => {
                    // add test infix
                    assert_eq!(
                        ife.consequence.statements.len(),
                        1,
                        "consequence is not 1 stmt, got {}",
                        ife.consequence.statements.len()
                    );
                    match ife.consequence.statements[0].clone() {
                        Statement::Expression(exp) => {
                            assert_eq!(
                                exp.token.to_string(),
                                "x",
                                "did not get x, got {}",
                                exp.token.to_string()
                            )
                        }
                        _ => println!(
                            "statement[0] is not an expression, got {}",
                            ife.consequence.statements[0].to_string()
                        ),
                    }
                    assert!(
                        ife.alternative.is_some(),
                        "alt is not something, got {:?}",
                        ife.alternative
                    )
                }
                _ => print!("expr is not an if, got {}", s.to_string()),
            },
            _ => println!("stmt is not an expression, got {}", s.to_string()),
        };
    }
    println!("Passed test if else expressions");
}

pub fn test_function_literal_parsing() {
    let input = "fn(x, y) { x + y; }";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "program body does not contain 1 statement, got {}",
            prog.statements.len()
        );
        let s = prog.statements[0].clone();
        match &s {
            Statement::Expression(expr) => match *expr.expression.clone().unwrap() {
                Expression::Fn(fe) => {
                    assert_eq!(
                        fe.params.len(),
                        2,
                        "fn params wrong, want 2, got {}",
                        fe.params.len()
                    );
                    assert_eq!(
                        fe.params[0].to_string(),
                        "x",
                        "p0 supposed to be x, got {}",
                        fe.params[0].to_string()
                    );
                    assert_eq!(
                        fe.params[1].to_string(),
                        "y",
                        "p1 supposed to be y, got {}",
                        fe.params[1].to_string()
                    );
                    assert_eq!(
                        fe.body.statements.len(),
                        1,
                        "body supposed to have 1 statement, got {}",
                        fe.body.statements.len()
                    );
                    match fe.body.statements[0].clone() {
                        Statement::Expression(be) => {
                            assert_eq!(
                                be.expression.clone().unwrap().to_string(),
                                "(x + y)",
                                "function didnt match, wanted (x + y) got {}",
                                be.expression.unwrap().to_string()
                            )
                        }
                        _ => println!(
                            "body should be expr, got {}",
                            fe.body.statements[0].to_string()
                        ),
                    }
                }
                _ => println!(
                    "didn't get a fn, got {}",
                    expr.expression.clone().unwrap().to_string()
                ),
            },
            _ => println!("stmt is not expr, got {}", &s.to_string()),
        }
    }
    println!("Passed test parse function literal")
}

pub fn test_function_param_parsing() {
    let tests = vec![
        ("fn() {};", vec![]),
        ("fn(x) {};", vec!["x"]),
        ("fn(x, y, z) {};", vec!["x", "y", "z"]),
    ];
    for t in tests {
        let l = Lexer::new(t.0.to_string());
        let mut p = Parser::new(l);
        let program = p.parse_program();
        let errors = p.check_errors();
        if errors {
            process::exit(1);
        }
        if let Some(prog) = program {
            let s = prog.statements[0].clone();
            match &s {
                Statement::Expression(expr) => match *expr.expression.clone().unwrap() {
                    Expression::Fn(fe) => {
                        assert_eq!(
                            fe.params.len(),
                            t.1.len(),
                            "length of params wrong, want {}, got {}",
                            t.1.len(),
                            fe.params.len()
                        );
                        for (p, test_p) in t.1.iter().zip(fe.params) {
                            assert_eq!(
                                &test_p.to_string().as_str(),
                                p,
                                "params don't match, want {}, got {}",
                                p,
                                test_p.to_string()
                            )
                        }
                    }
                    _ => println!(
                        "didn't get a fn, got {}",
                        expr.expression.clone().unwrap().to_string()
                    ),
                },
                _ => println!("stmt is not expr, got {}", &s.to_string()),
            }
        }
    }
    println!("Passed test parse function params")
}

pub fn test_call_expression() {
    let input = "add(1, 2 * 3, 4 + 5);";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        assert_eq!(
            prog.statements.len(),
            1,
            "length of params wrong, want 1, got {}",
            prog.statements.len()
        );
        match &prog.statements[0] {
            Statement::Expression(e) => match *e.expression.clone().unwrap() {
                Expression::Call(ce) => {
                    assert_eq!(
                        ce.func.to_string(),
                        "add",
                        "fn is not add, got {}",
                        ce.func.to_string()
                    );
                    assert_eq!(ce.args.len(), 3, "args len is not 3, got {}", ce.args.len());
                    // test args work
                }
                _ => println!(
                    "exp is not a call expr, got {}",
                    e.expression.clone().unwrap().to_string()
                ),
            },
            _ => println!(
                "stmt is not an expression, got {}",
                prog.statements[0].to_string()
            ),
        }
    }
    println!("Passed test parse call expression")
}

pub fn test_string_literal_expression() {
    let input = "\"hello world\"";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        match &prog.statements[0] {
            Statement::Expression(e) => match *e.expression.clone().unwrap() {
                Expression::StringLit(sle) => {
                    assert_eq!(
                        sle.value, "hello world",
                        "value not 'hello world' got {}",
                        sle.value
                    )
                }
                _ => println!(
                    "expr is not a string, got {}",
                    e.expression.clone().unwrap().to_string()
                ),
            },
            _ => println!("Not an expr, got {}", prog.statements[0].to_string()),
        }
    }
    println!("Passed test string literal expression");
}

pub fn test_parsing_array_literal() {
    let input = "[1, 2 * 2, 3 + 3]";
    let l = Lexer::new(input.to_string());
    let mut p = Parser::new(l);
    let program = p.parse_program();
    let errors = p.check_errors();
    if errors {
        process::exit(1);
    }
    if let Some(prog) = program {
        match &prog.statements[0] {
            Statement::Expression(e) => match *e.expression.clone().unwrap() {
                Expression::ArrayLit(ale) => {
                    assert_eq!(
                        ale.elements.len(),
                        3,
                        "len elements not 3, got {}",
                        ale.elements.len()
                    );
                    test_integer_literal(*ale.elements[0].clone().unwrap(), 1);
                    assert_eq!(
                        ale.elements[0].clone().unwrap().to_string(),
                        "1",
                        "a[0] not equal to 1, got {}",
                        ale.elements[0].clone().unwrap().to_string()
                    );
                    assert_eq!(
                        ale.elements[1].clone().unwrap().to_string(),
                        "(2 * 2)",
                        "a[1] not equal to (2 * 2), got {}",
                        ale.elements[1].clone().unwrap().to_string()
                    );
                    assert_eq!(
                        ale.elements[2].clone().unwrap().to_string(),
                        "(3 + 3)",
                        "a[2] not equal to (3 + 3), got {}",
                        ale.elements[2].clone().unwrap().to_string()
                    );
                }
                _ => println!(
                    "expr is not an array, got {}",
                    e.expression.clone().unwrap().to_string()
                ),
            },
            _ => println!("Not an expr, got {}", prog.statements[0].to_string()),
        }
    }
    println!("Passed test parsing array literal");
}
