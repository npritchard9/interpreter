mod lexer;
mod parser;
mod repl;

fn main() {
    //repl::start();
    parser::test_let_statements();
    parser::test_return_statements();
    parser::test_string();
    parser::test_identifier_expression();
    parser::test_integer_literal_expression();
    parser::test_prefix_expressions();
    parser::test_infix_expressions();
}
