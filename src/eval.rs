use crate::{
    lexer::Lexer,
    object::{Int, Object},
    parser::{Expression, Node, Parser, Statement},
};

pub fn eval(node: Node) -> Object {
    match node {
        Node::Expr(e) => match e {
            Expression::IntLit(ile) => return Object::Int(Int { value: ile.value }),
            _ => println!("not an int lit, got {}", e.to_string()),
        },
        Node::Prog(p) => return eval_stmts(p.statements),
        Node::Stmt(s) => match s {
            Statement::Expression(es) => return eval(Node::Expr(*es.expression.unwrap())),
            _ => println!("not an expr stmt, got {}", s.to_string()),
        },
    }
    Object::Null
}

pub fn eval_stmts(stmts: Vec<Statement>) -> Object {
    let mut res = Object::Null;
    for s in stmts {
        res = eval(Node::Stmt(s))
    }
    res
}

pub fn test_eval_int_expression() {
    let tests = vec![("5", 5), ("10", 10)];
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
