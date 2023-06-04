use std::collections::HashMap;

use crate::object::Object;

#[derive(Clone)]
pub struct Environment {
    store: HashMap<String, Object>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            store: HashMap::new(),
        }
    }

    pub fn get(&self, k: String) -> Option<&Object> {
        self.store.get(&k)
    }

    pub fn set(&mut self, k: String, v: Object) -> Option<Object> {
        self.store.insert(k, v)
    }

    pub fn show(&self) {
        println!("env: {:#?}", self.store);
    }
}
