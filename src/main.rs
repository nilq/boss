extern crate colored;

mod boss;

use self::boss::source::*;
use self::boss::lexer::*;
use self::boss::parser::*;
use self::boss::visitor::*;

fn main() {
  let test = r#"
a: i32 = 1

Foo: struct {
  x: i8
  y: i8
}

implement Foo {
  get_x: fun(self) -> i8 {
    self x + 10 as i8
  }
}

fib: fun(x: i32) -> Foo {
  foo := new Foo {
    x: 0
    y: 0
  }

  foo
}

{
  a: f32 = 10.0 + 100 as f32

  b: Foo = fib(10)

  fib := 100 as u8

  b: i8 = b get_x()
}
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