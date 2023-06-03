use std::any::Any;

use crate::{
    lexer::Lexer,
    object::{Bool, Int, Object},
    parser::{Expression, Node, Parser, Statement},
};

const TRUE: Object = Object::Bool(Bool { value: true });
const FALSE: Object = Object::Bool(Bool { value: false });
const NULL: Object = Object::Null;

pub fn eval(node: Node) -> Object {
    match node {
        Node::Expr(e) => match e {
            Expression::IntLit(ile) => return Object::Int(Int { value: ile.value }),
            Expression::BoolLit(ble) => {
                return match ble.value {
                    true => TRUE,
                    false => FALSE,
                }
            }
            Expression::Prefix(pe) => {
                let right = eval(Node::Expr(*pe.right.unwrap()));
                return eval_prefix_expression(pe.op, right);
            }
            _ => println!("not an int lit, got {}", e.to_string()),
        },
        Node::Prog(p) => return eval_stmts(p.statements),
        Node::Stmt(s) => match s {
            Statement::Expression(es) => return eval(Node::Expr(*es.expression.unwrap())),
            _ => println!("not an expr stmt, got {}", s.to_string()),
        },
    }
    NULL
}

pub fn eval_stmts(stmts: Vec<Statement>) -> Object {
    let mut res = Object::Null;
    for s in stmts {
        res = eval(Node::Stmt(s))
    }
    res
}

pub fn eval_prefix_expression(op: String, right: Object) -> Object {
    match op.as_str() {
        "!" => return eval_bang_op_expression(right),
        "-" => return eval_minus_prefix_op_expression(right),
        _ => NULL,
    }
}

pub fn eval_bang_op_expression(right: Object) -> Object {
    match right {
        Object::Bool(b) => match b.value {
            true => FALSE,
            false => TRUE,
        },
        Object::Null => TRUE,
        _ => FALSE,
    }
}

pub fn eval_minus_prefix_op_expression(right: Object) -> Object {
    match right {
        Object::Int(i) => Object::Int(Int { value: -i.value }),
        _ => NULL,
    }
}

// TESTS

pub fn test_eval_int_expression() {
    let tests = vec![("5", 5), ("10", 10), ("-5", -5), ("-10", -10)];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        if let Some(e) = evaluated {
            test_int_object(e, t.1);
        }
    }
    println!("passed test eval int expr");
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
            if i.value != expected {
                println!("obj has wrong value, wanted {}, got {}", expected, i.value);
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

pub fn test_eval_bool_expression() {
    let tests = vec![("true", true), ("false", false)];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        if let Some(e) = evaluated {
            test_bool_object(e, t.1);
        }
    }
    println!("Passed test eval bool expression")
}

pub fn test_bool_object(obj: Object, expected: bool) -> bool {
    match obj {
        Object::Bool(b) => {
            if b.value != expected {
                println!("obj has wrong value, wanted {}, got {}", expected, b.value);
                return false;
            }
        }
        _ => {
            println!("obj not bool, got {}", obj.to_string());
            return false;
        }
    }
    true
}

pub fn test_bang_operator() {
    let tests = vec![
        ("!true", false),
        ("!false", true),
        ("!5", false),
        ("!!true", true),
        ("!!false", false),
        ("!!5", true),
    ];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        test_bool_object(evaluated.unwrap(), t.1);
    }
    println!("Passed test bang op");
}
