use crate::{
    environment::{new_enclosed_env, Environment},
    lexer::{Lexer, Token},
    object::{self, Bool, Err, Function, Integer, OString, Object},
    parser::{BlockStatement, Expression, If, Node, Parser, Program, Statement},
};

const TRUE: Object = Object::Bool(Bool { value: true });
const FALSE: Object = Object::Bool(Bool { value: false });
const NULL: Object = Object::Null;

pub fn eval(node: Node, env: &mut Environment) -> Object {
    match node {
        Node::Expr(e) => match e {
            Expression::IntLit(ile) => return Object::Int(Integer { value: ile.value }),
            Expression::BoolLit(ble) => {
                return match ble.value {
                    true => TRUE,
                    false => FALSE,
                }
            }
            Expression::StringLit(sle) => {
                return Object::String(object::OString { value: sle.value })
            }
            Expression::Prefix(pe) => {
                let right = eval(Node::Expr(*pe.right.unwrap()), env);
                if is_error(right.clone()) {
                    return right;
                }
                return eval_prefix_expression(pe.op, right);
            }
            Expression::Infix(ie) => {
                let left = eval(Node::Expr(*ie.left.unwrap()), env);
                if is_error(left.clone()) {
                    return left;
                }
                let right = eval(Node::Expr(*ie.right.unwrap()), env);
                if is_error(right.clone()) {
                    return right;
                }
                return eval_infix_expression(ie.op, left, right);
            }
            Expression::If(ife) => return eval_if_expression(ife, env),
            Expression::Fn(fne) => {
                let params = fne.params;
                let body = fne.body;
                return Object::Func(Function {
                    params,
                    env: env.clone(),
                    body,
                });
            }
            Expression::Call(ce) => {
                let func = eval(Node::Expr(*ce.func), env);
                if is_error(func.clone()) {
                    return func;
                }
                let args = eval_expressions(ce.args, env);
                if args.len() == 1 && is_error(args[0].clone()) {
                    return args[0].clone();
                }
                return apply_function(func, args);
            }
            Expression::Id(ide) => return eval_ident(ide, env),
        },
        Node::Prog(p) => return eval_program(p, env),
        Node::Stmt(s) => match s {
            Statement::Expression(es) => match es.expression {
                Some(e) => return eval(Node::Expr(*e), env),
                None => return NULL,
            },
            Statement::Block(bs) => return eval_block_statement(bs, env),
            Statement::Return(rs) => {
                let val = eval(Node::Expr(*rs.value.unwrap()), env);
                if is_error(val.clone()) {
                    return val;
                }
                return Object::Return(object::Return {
                    value: Box::new(val),
                });
            }
            Statement::Let(ls) => {
                let val = eval(Node::Expr(*ls.value.unwrap()), env);
                if is_error(val.clone()) {
                    return val;
                }
                env.set(ls.name.to_string(), val);
            }
        },
    }
    NULL
}

pub fn apply_function(func: Object, args: Vec<Object>) -> Object {
    match func {
        Object::Func(f) => {
            let mut extended_env = extend_function_env(f.clone(), args);
            let evaluated = eval(Node::Stmt(Statement::Block(f.body)), &mut extended_env);
            unwrap_return_value(evaluated)
        }
        _ => {
            let msg = format!("not a function: {}", func.get_type());
            Object::Error(Err { msg })
        }
    }
}

pub fn extend_function_env(func: Function, args: Vec<Object>) -> Environment {
    let mut env = new_enclosed_env(func.env);
    for (i, p) in func.params.iter().enumerate() {
        env.set(p.to_string(), args[i].clone());
    }
    env
}

pub fn unwrap_return_value(obj: Object) -> Object {
    match obj {
        Object::Return(r) => *r.value,
        _ => obj,
    }
}

pub fn eval_expressions(exps: Vec<Option<Box<Expression>>>, env: &mut Environment) -> Vec<Object> {
    let mut res = Vec::new();
    for e in exps.iter() {
        let evaluated = eval(Node::Expr(*e.clone().unwrap()), env);
        if is_error(evaluated.clone()) {
            return vec![evaluated];
        }
        res.push(evaluated);
    }
    res
}

pub fn eval_ident(token: Token, env: &mut Environment) -> Object {
    match env.get(token.to_string()) {
        Some(v) => v,
        None => {
            let msg = format!("identifier not found: {}", token.to_string());
            Object::Error(Err { msg })
        }
    }
}

pub fn eval_if_expression(ife: If, env: &mut Environment) -> Object {
    match ife.cond {
        Some(c) => {
            let cond = eval(Node::Expr(*c), env);
            if is_truthy(cond) {
                eval(Node::Stmt(Statement::Block(ife.consequence)), env)
            } else if ife.alternative.is_some() {
                return eval(Node::Stmt(Statement::Block(ife.alternative.unwrap())), env);
            } else {
                NULL
            }
        }
        None => NULL,
    }
}

pub fn eval_block_statement(block: BlockStatement, env: &mut Environment) -> Object {
    let mut res = Object::Null;
    for s in block.statements {
        res = eval(Node::Stmt(s), env);
        match res {
            Object::Return(_) | Object::Error(_) => return res,
            _ => continue,
        }
    }
    res
}

pub fn is_truthy(obj: Object) -> bool {
    match obj {
        Object::Null => false,
        _ => obj == TRUE,
    }
}

pub fn is_error(obj: Object) -> bool {
    matches!(obj, Object::Error(_))
}

pub fn eval_program(p: Program, env: &mut Environment) -> Object {
    let mut res = Object::Null;
    for s in p.statements {
        res = eval(Node::Stmt(s), env);
        match res.clone() {
            Object::Return(r) => return *r.value,
            Object::Error(_) => return res,
            _ => continue,
        }
    }
    res
}

pub fn eval_prefix_expression(op: String, right: Object) -> Object {
    match op.as_str() {
        "!" => eval_bang_op_expression(right),
        "-" => eval_minus_prefix_op_expression(right),
        _ => {
            // check this msg val
            let msg = format!("unknown operator: {}{}", op, right.get_type());
            Object::Error(Err { msg })
        }
    }
}

pub fn eval_infix_expression(op: String, left: Object, right: Object) -> Object {
    match op.as_str() {
        "==" => Object::Bool(Bool {
            value: left == right,
        }),
        "!=" => {
            // should change this to use bool func
            Object::Bool(Bool {
                value: left != right,
            })
        }
        _ => match left {
            Object::Int(li) => match right {
                Object::Int(ri) => eval_int_infix_expression(op, li, ri),
                _ => {
                    let msg = format!(
                        "type mismatch: {} {} {}",
                        left.get_type(),
                        op,
                        right.get_type()
                    );
                    Object::Error(Err { msg })
                }
            },
            Object::String(ref ls) => match right {
                Object::String(rs) => eval_string_infix_expression(op, ls.clone(), rs),
                _ => {
                    let msg = format!(
                        "type mismatch: {} {} {}",
                        left.get_type(),
                        op,
                        right.get_type()
                    );
                    Object::Error(Err { msg })
                }
            },
            _ => {
                // check this msg val
                let msg = format!(
                    "unknown operator: {} {} {}",
                    left.get_type(),
                    op,
                    right.get_type()
                );
                Object::Error(Err { msg })
            }
        },
    }
}

pub fn eval_string_infix_expression(op: String, left: OString, right: OString) -> Object {
    let mut left_val = left.value;
    let right_val = right.value;
    match op.as_str() {
        "+" => {
            left_val.push_str(right_val.as_str());
            Object::String(OString { value: left_val })
        }
        _ => {
            let msg = format!(
                "unknown operator: {} {} {}",
                OString::get_type(),
                op,
                OString::get_type()
            );
            Object::Error(Err { msg })
        }
    }
}

pub fn eval_int_infix_expression(op: String, left: Integer, right: Integer) -> Object {
    let left_val = left.value;
    let right_val = right.value;
    match op.as_str() {
        "+" => Object::Int(Integer {
            value: left_val + right_val,
        }),
        "-" => Object::Int(Integer {
            value: left_val - right_val,
        }),
        "*" => Object::Int(Integer {
            value: left_val * right_val,
        }),
        "/" => Object::Int(Integer {
            value: left_val / right_val,
        }),
        "<" => Object::Bool(Bool {
            value: left_val < right_val,
        }),
        ">" => Object::Bool(Bool {
            value: left_val > right_val,
        }),
        "==" => Object::Bool(Bool {
            value: left_val == right_val,
        }),
        "!=" => Object::Bool(Bool {
            value: left_val != right_val,
        }),
        _ => {
            let msg = format!(
                "unknown operator: {} {} {}",
                Integer::get_type(),
                op,
                Integer::get_type()
            );
            Object::Error(Err { msg })
        }
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
        Object::Int(i) => Object::Int(Integer { value: -i.value }),
        _ => {
            let msg = format!("unknown operator: -{}", right.get_type());
            Object::Error(Err { msg })
        }
    }
}

// TESTS

pub fn test_eval_int_expression(_env: &mut Environment) {
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
    let mut e = Environment::new();
    program.map(|prog| eval(Node::Prog(prog), &mut e))
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

pub fn test_eval_bool_expression(_env: &mut Environment) {
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

pub fn test_bang_operator(_env: &mut Environment) {
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

pub fn test_if_else_expression(_env: &mut Environment) {
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
            Int(i) => assert!(
                test_int_object(evaluated.unwrap(), i),
                "didnt get true for int object"
            ),
            Obj(_) => assert!(
                test_null_object(evaluated.unwrap()),
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

pub fn test_return_statements(_env: &mut Environment) {
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
        assert!(
            test_int_object(evaluated.unwrap(), t.1),
            "didnt get true for return"
        )
    }
    println!("Passed test return statements")
}

pub fn test_error_handling(_env: &mut Environment) {
    let tests = vec![
        ("5 + true;", "type mismatch: INTEGER + BOOLEAN"),
        ("5 + true; 5;", "type mismatch: INTEGER + BOOLEAN"),
        ("-true", "unknown operator: -BOOLEAN"),
        ("true + false;", "unknown operator: BOOLEAN + BOOLEAN"),
        ("5; true + false; 5", "unknown operator: BOOLEAN + BOOLEAN"),
        (
            "if (10 > 1) { true + false; }",
            "unknown operator: BOOLEAN + BOOLEAN",
        ),
        (
            r#"if (10 > 1) {
                if (10 > 1) {
                    return true + false;
                }
                return 1;
            }"#,
            "unknown operator: BOOLEAN + BOOLEAN",
        ),
        ("foobar", "identifier not found: foobar"),
        (
            "\"Hello\" - \"World!\"",
            "unknown operator: STRING - STRING",
        ),
    ];

    for t in tests {
        let evaluated = test_eval(t.0.to_string());
        match evaluated {
            Some(eval) => match eval {
                Object::Error(e) => {
                    assert_eq!(e.msg, t.1, "wrong error msg, want {}, got {}", t.1, e.msg)
                }
                _ => println!(
                    "obj isnt an error, got {} with {}",
                    eval.to_string(),
                    eval.get_type()
                ),
            },
            None => continue,
        }
    }
    println!("Passed test error handling")
}

pub fn test_let_statements(_env: &mut Environment) {
    let tests = vec![
        ("let a = 5; a;", 5),
        ("let a = 5 * 5; a;", 25),
        ("let a = 5; let b = a; b;", 5),
        ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
    ];
    for t in tests {
        test_int_object(test_eval(t.0.to_string()).unwrap(), t.1);
    }
}

pub fn test_function_object() {
    let input = "fn(x) { x + 2; };";
    let evaluated = test_eval(input.to_string());
    if let Some(e) = evaluated {
        match e {
            Object::Func(f) => {
                assert_eq!(f.params.len(), 1, "fn has wrong params, got {:?}", f.params);
                assert_eq!(
                    f.params[0].to_string(),
                    "x",
                    "param is not x, got {}",
                    f.params[0].to_string()
                );
                assert_eq!(
                    f.body.to_string(),
                    "(x + 2)",
                    "body is wrong, got {}",
                    f.body.to_string()
                )
            }
            _ => println!("obj not a function, got {}", e.to_string()),
        }
    }
    println!("Passed test function object")
}

pub fn test_function_application() {
    let tests = vec![
        ("let identity = fn(x) { x; }; identity(5);", 5),
        ("let identity = fn(x) { return x; }; identity(5);", 5),
        ("let double = fn(x) { x * 2; }; double(5);", 10),
        ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
        ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
        ("fn(x) { x; }(5)", 5),
    ];
    for t in tests {
        test_int_object(test_eval(t.0.to_string()).unwrap(), t.1);
    }
    println!("Passed test function application");
}

pub fn test_closures() {
    let input = r#"
        let newAdder = fn(x) {
            fn(y) { x + y };
        };
        let addTwo = newAdder(2);
        addTwo(2);
        "#;
    test_int_object(test_eval(input.to_string()).unwrap(), 4);
    println!("Passed test closures");
}

pub fn test_string_literal() {
    let input = "\"Hello World!\"";
    let evaluated = test_eval(input.to_string());
    match evaluated.clone().unwrap() {
        Object::String(s) => {
            assert_eq!(
                s.value, "Hello World!",
                "string has wrong value, got {}",
                s.value
            )
        }
        _ => println!(
            "Not a string, got {}",
            evaluated.unwrap().to_string()
        ),
    }
    println!("Passed test string literal")
}

pub fn test_string_concat() {
    let input = "\"Hello\" + \" \" + \"World!\"";
    let evaluated = test_eval(input.to_string());
    match evaluated.clone().unwrap() {
        Object::String(s) => {
            assert_eq!(
                s.value, "Hello World!",
                "string has wrong value, got {}",
                s.value
            )
        }
        _ => println!(
            "Not a string, got {}",
            evaluated.unwrap().to_string()
        ),
    }
    println!("Passed test string concat")
}
