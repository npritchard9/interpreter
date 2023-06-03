pub enum Object {
    Int(Int),
    Bool(Bool),
    Null,
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::Int(i) => format!("{}", i.value),
            Object::Bool(b) => format!("{}", b.value),
            Object::Null => "null".to_string(),
        }
    }
}

pub struct Int {
    pub value: isize,
}

pub struct Bool {
    pub value: bool,
}
