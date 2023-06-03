pub enum Object {
    Int(Int),
    Bool(Bool),
    Null,
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::Int(i) => format!("{}", i.val),
            Object::Bool(b) => format!("{}", b.val),
            Object::Null => "null".to_string(),
        }
    }
}

pub struct Int {
    pub val: isize,
}
pub struct Bool {
    pub val: bool,
}
