use crate::{
    lexer::Lexer,
    object::Object,
    parser::{Node, Parser},
};

pub fn eval(node: Node) -> Object {
    print!("hi");
    Object::Null
}

pub fn test_eval_int_expression() {
    let tests = vec![("5", 5), ("10", 10)];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        if let Some(e) = evaluated {
            test_int_object(e, t.1);
        }
    }
}

pub fn test_eval(input: String) -> Option<Object> {
    let l = Lexer::new(input);
    let mut p = Parser::new(l);
    let program = p.parse_program();
    if let Some(prog) = program {
        Some(eval(Node::Prog(prog)))
    } else {
        None
    }
}

pub fn test_int_object(obj: Object, expected: isize) -> bool {
    match obj {
        Object::Int(i) => {
            if i.val != expected {
                println!("obj has wrong value, wanted {}, got {}", expected, i.val);
                return false;
            }
        }
        _ => {
            println!("obj not int, got {}", obj.to_string());
            return false;
        }
    }
    true
}
