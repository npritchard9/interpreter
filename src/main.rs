mod eval;
mod lexer;
mod object;
mod parser;
mod repl;

fn main() {
    // repl::start();
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
    eval::test_eval_int_expression();
}
