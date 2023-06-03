use crate::{
    lexer::Lexer,
    object::{self, Bool, Int, Object, Return},
    parser::{BlockStatement, Expression, If, Node, Parser, Program, Statement},
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
            Expression::Infix(ie) => {
                let left = eval(Node::Expr(*ie.left.unwrap()));
                let right = eval(Node::Expr(*ie.right.unwrap()));
                return eval_infix_expression(ie.op, left, right);
            }
            Expression::If(ife) => return eval_if_expression(ife),
            _ => println!("not an int lit, got {}", e.to_string()),
        },
        Node::Prog(p) => return eval_program(p),
        Node::Stmt(s) => match s {
            Statement::Expression(es) => match es.expression {
                Some(e) => return eval(Node::Expr(*e)),
                None => return NULL,
            },
            Statement::Block(bs) => return eval_block_statement(bs),
            Statement::Return(rs) => {
                let val = eval(Node::Expr(*rs.value.unwrap()));
                return Object::Return(object::Return {
                    value: Box::new(val),
                });
            }
            _ => println!("not an expr stmt, got {}", s.to_string()),
        },
    }
    NULL
}

pub fn eval_if_expression(ife: If) -> Object {
    match ife.cond {
        Some(c) => {
            let cond = eval(Node::Expr(*c));
            if is_truthy(cond) {
                return eval(Node::Stmt(Statement::Block(ife.consequence)));
            } else if ife.alternative.is_some() {
                return eval(Node::Stmt(Statement::Block(ife.alternative.unwrap())));
            } else {
                NULL
            }
        }
        None => NULL,
    }
}

pub fn eval_block_statement(block: BlockStatement) -> Object {
    let mut res = Object::Null;
    for s in block.statements {
        res = eval(Node::Stmt(s));
        return res;
    }
    return res;
}

pub fn is_truthy(obj: Object) -> bool {
    match obj {
        Object::Null => false,
        _ => obj == TRUE,
    }
}

pub fn eval_program(p: Program) -> Object {
    let mut res = Object::Null;
    for s in p.statements {
        res = eval(Node::Stmt(s));
        if let Object::Return(r) = res {
            match *r.value {
                Object::Int(i) => return Object::Int(Int { value: i.value }),
                Object::Bool(b) => return Object::Bool(Bool { value: b.value }),
                Object::Return(rv) => return Object::Return(Return { value: rv.value }),
                _ => return NULL,
            }
        }
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

pub fn eval_infix_expression(op: String, left: Object, right: Object) -> Object {
    match op.as_str() {
        "==" => {
            return Object::Bool(Bool {
                value: left == right,
            })
        }
        "!=" => {
            // should change this to use bool func
            return Object::Bool(Bool {
                value: left != right,
            });
        }
        _ => match left {
            Object::Int(li) => match right {
                Object::Int(ri) => eval_int_infix_expression(op, li, ri),
                _ => NULL,
            },
            _ => NULL,
        },
    }
}

pub fn eval_int_infix_expression(op: String, left: Int, right: Int) -> Object {
    let left_val = left.value;
    let right_val = right.value;
    match op.as_str() {
        "+" => {
            return Object::Int(Int {
                value: left_val + right_val,
            })
        }
        "-" => {
            return Object::Int(Int {
                value: left_val - right_val,
            })
        }
        "*" => {
            return Object::Int(Int {
                value: left_val * right_val,
            })
        }
        "/" => {
            return Object::Int(Int {
                value: left_val / right_val,
            })
        }
        "<" => {
            return Object::Bool(Bool {
                value: left_val < right_val,
            })
        }
        ">" => {
            return Object::Bool(Bool {
                value: left_val > right_val,
            })
        }
        "==" => {
            return Object::Bool(Bool {
                value: left_val == right_val,
            })
        }
        "!=" => {
            return Object::Bool(Bool {
                value: left_val != right_val,
            })
        }
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
    let tests = vec![
        ("5", 5),
        ("10", 10),
        ("-5", -5),
        ("-10", -10),
        ("5 + 5 + 5 + 5 - 10", 10),
        ("2 * 2 * 2 * 2 * 2", 32),
        ("-50 + 100 + -50", 0),
        ("5 * 2 + 10", 20),
        ("5 + 2 * 10", 25),
        ("20 + 2 * -10", 0),
        ("50 / 2 * 2 + 10", 60),
        ("2 * (5 + 10)", 30),
        ("3 * 3 * 3 + 10", 37),
        ("3 * (3 * 3) + 10", 37),
        ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
    ];
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
            println!("obj not int, wanted {}, got {}", expected, obj.to_string());
            return false;
        }
    }
    true
}

pub fn test_eval_bool_expression() {
    let tests = vec![
        ("true", true),
        ("false", false),
        ("1 < 2", true),
        ("1 > 2", false),
        ("1 < 1", false),
        ("1 > 1", false),
        ("1 == 1", true),
        ("1 != 1", false),
        ("1 == 2", false),
        ("1 != 2", true),
        ("true == true", true),
        ("false == false", true),
        ("true == false", false),
        ("true != false", true),
        ("false != true", true),
        ("(1 < 2) == true", true),
        ("(1 < 2) == false", false),
        ("(1 > 2) == true", false),
        ("(1 > 2) == false", true),
    ];
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

pub fn test_if_else_expression() {
    enum IfElseRes {
        Int(isize),
        Obj(Object),
    }
    use IfElseRes::*;
    let tests: Vec<(&str, IfElseRes)> = vec![
        ("if (true) { 10 }", Int(10)),
        ("if (false) { 10 }", Obj(NULL)),
        ("if (1) { 10 }", Int(10)),
        ("if (1 < 2) { 10 }", Int(10)),
        ("if (1 > 2) { 10 }", Obj(NULL)),
        ("if (1 > 2) { 10 } else { 20 }", Int(20)),
        ("if (1 < 2) { 10 } else { 20 }", Int(10)),
    ];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        match t.1 {
            Int(i) => assert_eq!(
                test_int_object(evaluated.unwrap(), i),
                true,
                "didnt get true for int object"
            ),
            Obj(_) => assert_eq!(
                test_null_object(evaluated.unwrap()),
                true,
                "didnt get true for null object"
            ),
        }
    }
}

pub fn test_null_object(obj: Object) -> bool {
    if let Object::Null = obj {
        return true;
    }
    false
}

pub fn test_return_statements() {
    let tests = vec![
        ("return 10;", 10),
        ("return 10; 9;", 10),
        ("return 2 * 5; 9;", 10),
        ("9; return 2 * 5; 9;", 10),
        (
            "if 10 > 1) {
            if (10 > 1) {
                return 10;
            }
            return 1;
        }",
            10,
        ),
    ];
    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        assert_eq!(
            test_int_object(evaluated.unwrap(), t.1),
            true,
            "didnt get true for return"
        )
    }
    println!("Passed test return statements")
}
