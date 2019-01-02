extern crate colored;

mod boss;

use self::boss::source::*;
use self::boss::lexer::*;
use self::boss::parser::*;
use self::boss::visitor::*;

fn main() {
  let test = r#"
a: i32 = r"hey"
  "#;

  let source = Source::from("<main>", test.lines().map(|x| x.into()).collect::<Vec<String>>());
  let lexer  = Lexer::default(test.chars().collect(), &source);

  let mut tokens = Vec::new();

  for token_result in lexer {
    if let Ok(token) = token_result {
      tokens.push(token)
    } else {
      return
    }
  }

  let mut parser = Parser::new(tokens, &source);

  match parser.parse() {
    Ok(ref ast) => {
      println!("{:#?}", ast);

      let mut visitor = Visitor::new(&ast, &source);

      visitor.visit();
    },

    _ => ()
  }
}