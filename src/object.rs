use crate::{environment::Environment, lexer::Token, parser::BlockStatement};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Int(Integer),
    Bool(Bool),
    String(OString),
    Return(Return),
    Func(Function),
    Error(Err),
    Null,
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::Int(i) => format!("{}", i.value),
            Object::Bool(b) => format!("{}", b.value),
            Object::String(s) => s.value.to_string(),
            Object::Null => "".to_string(),
            Object::Return(r) => r.value.to_string(),
            Object::Error(e) => e.to_string(),
            Object::Func(f) => f.to_string(),
        }
    }
}

impl Object {
    pub fn get_type(&self) -> String {
        match self {
            Object::Int(_) => String::from("INTEGER"),
            Object::Bool(_) => String::from("BOOLEAN"),
            Object::String(_) => String::from("STRING"),
            Object::Return(_) => String::from("RETURN"),
            Object::Error(e) => e.to_string(),
            Object::Null => String::from("NULL"),
            Object::Func(_) => String::from("FUNCTION"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Integer {
    pub value: isize,
}

impl Integer {
    pub fn get_type() -> String {
        String::from("INTEGER")
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OString {
    pub value: String,
}

impl OString {
    pub fn get_type() -> String {
        String::from("STRING")
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Bool {
    pub value: bool,
}

impl Bool {
    fn get_type() -> String {
        String::from("BOOLEAN")
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Return {
    pub value: Box<Object>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Err {
    pub msg: String,
}

impl ToString for Err {
    fn to_string(&self) -> String {
        format!("Error: {}", self.msg)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Function {
    pub params: Vec<Token>,
    pub body: BlockStatement,
    pub env: Environment,
}

impl ToString for Function {
    fn to_string(&self) -> String {
        let mut params = vec![];
        for p in self.params.iter() {
            params.push(p.to_string())
        }
        format!(
            "fn({}) {{\n{}\n}}",
            params.join(", "),
            self.body.to_string()
        )
    }
}
