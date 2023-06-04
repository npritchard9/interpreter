use std::collections::HashMap;

use crate::object::Object;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Environment {
    pub store: HashMap<String, Object>,
    pub outer: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            store: HashMap::new(),
            outer: None,
        }
    }

    pub fn get(&self, k: String) -> Option<Object> {
        match self.store.get(&k) {
            Some(v) => Some(v.clone()),
            None => {
                if let Some(out) = self.outer.clone() {
                    return out.get(k);
                }
                None
            }
        }
    }

    pub fn set(&mut self, k: String, v: Object) -> Option<Object> {
        self.store.insert(k, v)
    }
}

pub fn new_enclosed_env(outer: Environment) -> Environment {
    let mut env = Environment::new();
    env.outer = Some(Box::new(outer));
    env
}
