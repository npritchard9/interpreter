use std::io;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
#[repr(usize)]
pub enum Token {
    // identifiers
    Ident(String) = 1,
    Int(String),

    // special case
    Eof,
    Illegal,

    // operators
    Assign,
    Asterisk,
    Bang,
    Equal,
    GreaterThan,
    LessThan,
    Minus,
    NotEqual,
    Plus,
    Slash,

    // delimiters
    Comma,
    Lbrace,
    Lparen,
    Rbrace,
    Rparen,
    Semicolon,

    // keywords
    Else,
    False,
    Function,
    If,
    Let,
    Return,
    True,
}

impl ToString for Token {
    fn to_string(&self) -> String {
        match self {
            Token::Ident(ident) => ident.to_string(),
            Token::Int(i) => i.to_string(),
            Token::Illegal => "Illegal".to_string(),
            Token::Eof => "Eof".to_string(),
            Token::Bang => "!".to_string(),
            Token::Slash => "/".to_string(),
            Token::Asterisk => "*".to_string(),
            Token::Equal => "==".to_string(),
            Token::NotEqual => "!=".to_string(),
            Token::LessThan => "<".to_string(),
            Token::GreaterThan => ">".to_string(),
            Token::Assign => "=".to_string(),
            Token::Plus => "+".to_string(),
            Token::Minus => "-".to_string(),
            Token::Comma => ",".to_string(),
            Token::Semicolon => ";".to_string(),
            Token::Lparen => "(".to_string(),
            Token::Rparen => ")".to_string(),
            Token::Lbrace => "{".to_string(),
            Token::Rbrace => "}".to_string(),
            Token::Function => "fn".to_string(),
            Token::Let => "let".to_string(),
            Token::If => "if".to_string(),
            Token::Else => "else".to_string(),
            Token::Return => "return".to_string(),
            Token::True => "true".to_string(),
            Token::False => "false".to_string(),
        }
    }
}

pub struct Lexer {
    pub input: Vec<u8>,
    pub pos: usize,
    pub read_pos: usize,
    pub ch: u8,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        let mut l = Lexer {
            input: input.into_bytes(),
            pos: 0,
            read_pos: 0,
            ch: 0,
        };
        l.read_char();
        l
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_ascii_whitespace() {
            self.read_char();
        }
    }

    fn read_char(&mut self) {
        if self.read_pos >= self.input.len() {
            self.ch = 0;
        } else {
            self.ch = self.input[self.read_pos];
        }
        self.pos = self.read_pos;
        self.read_pos += 1;
    }

    fn peek(&self) -> u8 {
        if self.read_pos >= self.input.len() {
            return 0;
        } else {
            return self.input[self.read_pos];
        }
    }

    pub fn next_token(&mut self) -> Result<Token, io::Error> {
        self.skip_whitespace();
        let tok = match self.ch {
            b'=' => {
                if self.peek() == b'=' {
                    self.read_char();
                    Token::Equal
                } else {
                    Token::Assign
                }
            }
            b';' => Token::Semicolon,
            b'(' => Token::Lparen,
            b')' => Token::Rparen,
            b',' => Token::Comma,
            b'+' => Token::Plus,
            b'-' => Token::Minus,
            b'{' => Token::Lbrace,
            b'}' => Token::Rbrace,
            b'!' => {
                if self.peek() == b'=' {
                    self.read_char();
                    Token::NotEqual
                } else {
                    Token::Bang
                }
            }
            b'/' => Token::Slash,
            b'*' => Token::Asterisk,
            b'>' => Token::GreaterThan,
            b'<' => Token::LessThan,
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                let ident = self.read_ident();
                return Ok(match ident.as_str() {
                    "fn" => Token::Function,
                    "let" => Token::Let,
                    "if" => Token::If,
                    "false" => Token::False,
                    "true" => Token::True,
                    "return" => Token::Return,
                    "else" => Token::Else,
                    _ => Token::Ident(ident),
                });
            }
            b'0'..=b'9' => return Ok(Token::Int(self.read_int())),
            0 => Token::Eof,
            _ => Token::Illegal,
        };
        self.read_char();
        Ok(tok)
    }

    fn read_ident(&mut self) -> String {
        let pos = self.pos;
        while self.ch.is_ascii_alphabetic() || self.ch == b'_' {
            self.read_char();
        }
        return String::from_utf8_lossy(&self.input[pos..self.pos]).to_string();
    }

    fn read_int(&mut self) -> String {
        let pos = self.pos;
        while self.ch.is_ascii_digit() {
            self.read_char();
        }
        return String::from_utf8_lossy(&self.input[pos..self.pos]).to_string();
    }
}

#[cfg(test)]
mod tests {
    use super::{Lexer, Token};

    #[test]
    fn test_next_token() {
        let input = String::from("=+(){},;");
        let tokens: Vec<Token> = vec![
            Token::Assign,
            Token::Plus,
            Token::Lparen,
            Token::Rparen,
            Token::Lbrace,
            Token::Rbrace,
            Token::Comma,
            Token::Semicolon,
            Token::Eof,
        ];

        let mut l = Lexer::new(input);

        for token in tokens {
            let tok = l.next_token().unwrap();
            assert_eq!(tok, token, "Error on token {token:?}");
        }
    }
    #[test]
    fn test_next_token2() {
        let input = r#"let five = 5;
            let ten = 10;
            let add = fn(x, y) {
                x + y;
            };
            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;
            if (5 < 10) {
                return true;
            } else {
                return false;
            }
            10 == 10;
            10 != 9;"#;

        let mut l = Lexer::new(input.into());
        let tokens = vec![
            Token::Let,
            Token::Ident(String::from("five")),
            Token::Assign,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("ten")),
            Token::Assign,
            Token::Int(String::from("10")),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("add")),
            Token::Assign,
            Token::Function,
            Token::Lparen,
            Token::Ident(String::from("x")),
            Token::Comma,
            Token::Ident(String::from("y")),
            Token::Rparen,
            Token::Lbrace,
            Token::Ident(String::from("x")),
            Token::Plus,
            Token::Ident(String::from("y")),
            Token::Semicolon,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("result")),
            Token::Assign,
            Token::Ident(String::from("add")),
            Token::Lparen,
            Token::Ident(String::from("five")),
            Token::Comma,
            Token::Ident(String::from("ten")),
            Token::Rparen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::Int(String::from("5")),
            Token::LessThan,
            Token::Int(String::from("10")),
            Token::GreaterThan,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::If,
            Token::Lparen,
            Token::Int(String::from("5")),
            Token::LessThan,
            Token::Int(String::from("10")),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::Rbrace,
            Token::Else,
            Token::Lbrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::Rbrace,
            Token::Int(String::from("10")),
            Token::Equal,
            Token::Int(String::from("10")),
            Token::Semicolon,
            Token::Int(String::from("10")),
            Token::NotEqual,
            Token::Int(String::from("9")),
            Token::Semicolon,
            Token::Eof,
        ];
        for token in tokens {
            let tok = l.next_token().unwrap();
            assert_eq!(tok, token, "Error on token {token:?}");
        }
    }
}
