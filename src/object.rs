#[derive(PartialEq, Eq)]
pub enum Object {
    Int(Int),
    Bool(Bool),
    Return(Return),
    Null,
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::Int(i) => format!("{}", i.value),
            Object::Bool(b) => format!("{}", b.value),
            Object::Null => "null".to_string(),
            Object::Return(r) => format!("{}", r.value.to_string()),
        }
    }
}

#[derive(PartialEq, Eq)]
pub struct Int {
    pub value: isize,
}

#[derive(PartialEq, Eq)]
pub struct Bool {
    pub value: bool,
}

#[derive(PartialEq, Eq)]
pub struct Return {
    pub value: Box<Object>,
}
