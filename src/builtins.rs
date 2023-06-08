use std::collections::HashMap;

use crate::object::{self, BuiltinFn, Object};

pub struct Builtins {
    pub fns: HashMap<String, BuiltinFn>,
}

pub fn len(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        let msg = format!("wrong number of arguments. got={}, want=1", args.len());
        return Object::Error(object::Err { msg });
    }
    match &args[0] {
        Object::String(s) => Object::Int(object::Integer {
            value: s.value.len() as isize,
        }),
        Object::Array(a) => Object::Int(object::Integer {
            value: a.elements.len() as isize,
        }),
        _ => {
            let msg = format!(
                "argument to 'len' not supported, got {}",
                args[0].get_type()
            );
            Object::Error(object::Err { msg })
        }
    }
}

pub fn first(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        let msg = format!("wrong number of arguments. got={}, want=1", args.len());
        return Object::Error(object::Err { msg });
    }
    match &args[0] {
        Object::Array(a) => a.elements[0].clone(),
        _ => {
            let msg = format!(
                "argument to 'first' must be array, got {}",
                args[0].get_type()
            );
            Object::Error(object::Err { msg })
        }
    }
}

pub fn last(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        let msg = format!("wrong number of arguments. got={}, want=1", args.len());
        return Object::Error(object::Err { msg });
    }
    match &args[0] {
        Object::Array(a) => a.elements.last().unwrap().clone(),
        _ => {
            let msg = format!(
                "argument to 'last' must be array, got {}",
                args[0].get_type()
            );
            Object::Error(object::Err { msg })
        }
    }
}

impl Builtins {
    pub fn new() -> Self {
        let mut h = HashMap::new();
        h.insert("len".to_string(), len as fn(Vec<Object>) -> Object);
        h.insert("first".to_string(), first as fn(Vec<Object>) -> Object);
        h.insert("last".to_string(), last as fn(Vec<Object>) -> Object);
        Builtins { fns: h }
    }
}
