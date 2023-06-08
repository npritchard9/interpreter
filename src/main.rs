// use environment::Environment;

mod builtins;
mod environment;
mod eval;
mod lexer;
mod object;
mod parser;
mod repl;

fn main() {
    // let mut env = Environment::new();
    repl::start();
    // parser::test_let_statements();
    // parser::test_return_statements();
    // parser::test_string();
    // parser::test_identifier_expression();
    // parser::test_integer_literal_expression();
    // parser::test_boolean_literal_expression();
    // parser::test_prefix_expressions();
    // parser::test_infix_expressions();
    // parser::test_operator_precedence_parsing();
    // parser::test_if_expression();
    // parser::test_if_else_expression();
    // parser::test_function_literal_parsing();
    // parser::test_function_param_parsing();
    // parser::test_call_expression();
    // eval::test_eval_int_expression(&mut env);
    // eval::test_eval_bool_expression(&mut env);
    // eval::test_bang_operator(&mut env);
    // eval::test_if_else_expression(&mut env);
    // eval::test_return_statements(&mut env);
    // eval::test_error_handling(&mut env);
    // eval::test_function_object();
    // eval::test_function_application();
    // eval::test_closures();
    // parser::test_string_literal_expression();
    // eval::test_string_literal();
    // eval::test_error_handling(&mut env);
    // eval::test_string_concat();
    // eval::test_builtin_fn();
    // parser::test_parsing_array_literal();
    // parser::test_parsing_index_expressions();
    // eval::test_array_literals();
    // eval::test_array_index_expressions();
}
