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

pub fn rest(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        let msg = format!("wrong number of arguments. got={}, want=1", args.len());
        return Object::Error(object::Err { msg });
    }
    match &args[0] {
        Object::Array(a) => {
            let len = a.elements.len();
            if len > 0 {
                return Object::Array(object::ArrObj {
                    elements: a.elements[1..].to_vec(),
                });
            }
            a.elements.last().unwrap().clone()
        }
        _ => {
            let msg = format!(
                "argument to 'rest' must be array, got {}",
                args[0].get_type()
            );
            Object::Error(object::Err { msg })
        }
    }
}

pub fn push(args: Vec<Object>) -> Object {
    if args.len() != 2 {
        let msg = format!("wrong number of arguments. got={}, want=2", args.len());
        return Object::Error(object::Err { msg });
    }
    match &args[0] {
        Object::Array(a) => {
            let len = a.elements.len();
            if len > 0 {
                let mut copy_els = a.elements.clone();
                copy_els.push(args[1].clone());
                return Object::Array(object::ArrObj { elements: copy_els });
            }
            a.elements.last().unwrap().clone()
        }
        _ => {
            let msg = format!(
                "argument to 'push' must be array, got {}",
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
        h.insert("rest".to_string(), rest as fn(Vec<Object>) -> Object);
        h.insert("push".to_string(), push as fn(Vec<Object>) -> Object);
        Builtins { fns: h }
    }
}
