#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Int(Integer),
    Bool(Bool),
    Return(Return),
    Error(Err),
    Null,
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::Int(i) => format!("{}", i.value),
            Object::Bool(b) => format!("{}", b.value),
            Object::Null => "".to_string(),
            Object::Return(r) => r.value.to_string(),
            Object::Error(e) => e.to_string(),
        }
    }
}

impl Object {
    pub fn get_type(&self) -> String {
        match self {
            Object::Int(_) => String::from("INTEGER"),
            Object::Bool(_) => String::from("BOOLEAN"),
            Object::Return(_) => String::from("RETURN"),
            Object::Error(e) => e.to_string(),
            Object::Null => String::from("NULL"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Integer {
    pub value: isize,
}

impl Integer {
    pub fn get_type() -> String {
        String::from("Integer")
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Bool {
    pub value: bool,
}

impl Bool {
    fn get_type() -> String {
        String::from("Bool")
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
