use std::fmt::{ self, Display, Write, Formatter };
use std::rc::Rc;
use std::collections::HashMap;

use super::super::error::Response::*;

use super::*;



use std::fs::File;
use std::io::prelude::*;
use std::path::Path;



#[derive(Debug, Clone)]
pub enum TypeNode {
  UInt(usize),  // byte size (u8, u16, u32, u64, u128)
  Int(usize),   // byte size (i8, i16, i32, i64, i128)
  Float(usize), // byte size (f32, f64, f128)
  Bool,
  Str,
  Any,
  Char,
  Nil,
  Id(Rc<Expression>),
  Array(Rc<Type>, Option<usize>),
  Func(Vec<Type>, Rc<Type>, Option<Rc<ExpressionNode>>, bool),
  Module(HashMap<String, Type>),
  Struct(String, HashMap<String, Type>, String),
  This,
}

impl TypeNode {
  pub fn check_expression(&self, other: &ExpressionNode) -> bool {
    use self::TypeNode::*;

    match *other {
      ExpressionNode::Int(_) => match *self {
        Int(_) | Float(_) | UInt(_) => true,
        _                           => false,
      },

      ExpressionNode::Array(ref content) => {
        let array_content = if let &Array(ref array_content, ref len) = self {
          
          if let Some(len) = len {
            if *len != content.len() {
              return false
            }
          }

          array_content
        } else {
          return false
        };

        for element in content {
          if !array_content.node.check_expression(&element.node) {
            return false
          }
        }

        true
      },

      _ => false
    }
  }

  pub fn strong_cmp(&self, other: &TypeNode) -> bool {
    use self::TypeNode::*;

    match (self, other) {
      (&Int(size_a), &Int(size_b))     => size_a == size_b,
      (&Float(size_a), &Float(size_b)) => size_a == size_b,
      (&Bool, &Bool)   => true,
      (&Str, &Str)     => true,
      (&Any, &Any)     => true,
      (&Char, &Char)   => true,
      (&This, &This)   => true,
      (&Id(ref a), &Id(ref b)) => a == b,
      (&Array(ref a, ref la), &Array(ref b, ref lb))                                     => a == b && (la == &None || la == lb),
      (&Func(ref a_params, ref a_retty, .., a), &Func(ref b_params, ref b_retty, .., b)) => a_params == b_params && a_retty == b_retty && a == b,
      (&Struct(ref name, _, ref content), &Struct(ref name_b, _, ref content_b))         => name == name_b && content == content_b,
      _ => false,
    }
  }
}

impl PartialEq for TypeNode {
  fn eq(&self, other: &Self) -> bool {
    use self::TypeNode::*;

    match (self, other) {
      (&Int(size_a),                         &Int(size_b))                         => size_a == size_b,
      (&Str,                                 &Str)                                 => true,
      (&Float(size_a),                       &Float(size_b))                       => size_a == size_b,
      (&Char,                                &Char)                                => true,
      (&Bool,                                &Bool)                                => true,
      (&Nil,                                 &Nil)                                 => true,
      (&This,                                &This)                                => true,
      (&Array(ref a, ref la),                &Array(ref b, ref lb))                => a == b && (la == &None || la == lb),
      (&Id(ref a),                           &Id(ref b))                           => a == b,
      (&Func(ref a_params, ref a_retty, .., a), &Func(ref b_params, ref b_retty, .., b)) => a_params == b_params && a_retty == b_retty && a == b,

      (&Struct(ref name, _, ref content), &Struct(ref name_b, _, ref content_b)) => name == name_b && content == content_b,

      (&Any, _) => true,
      (_, &Any) => true,

      _ => false,
    }
  }
}



#[derive(Debug, Clone)]
pub enum TypeMode {
  Undeclared,
  Immutable,
  Optional,
  Implemented,
  Regular,
  Splat(Option<usize>),
  Unwrap(usize),
}

impl TypeMode {
  pub fn check(&self, other: &TypeMode) -> bool {
    use self::TypeMode::*;

    match (self, other) {
      (&Regular,     &Regular)     => true,
      (&Immutable,   &Immutable)   => true,
      (&Optional,    &Optional)    => true,
      (&Implemented, &Implemented) => true,
      (&Undeclared,  &Undeclared)  => true,
      (&Splat(a),    &Splat(b))    => &a == &b,
      (&Unwrap(_),   &Unwrap(_))   => true,
      _                            => false,
    }
  }
}

impl Display for TypeNode {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    use self::TypeNode::*;

    match *self {
      UInt(size)       => write!(f, "u{}", size),
      Int(size)        => write!(f, "i{}", size),
      Float(size)      => write!(f, "f{}", size),
      Bool             => write!(f, "bool"),
      Str              => write!(f, "str"),
      Char             => write!(f, "char"),
      Nil              => write!(f, "nil"),
      This             => write!(f, "self"),
      Any              => write!(f, "any"),
      Array(ref n, l)  => if let Some(len) = l {
        write!(f, "[{}; {}]", n, len)
      } else {
        write!(f, "[{}]", n)
      },

      Id(ref n) => write!(f, "{}", n.pos.get_lexeme()),

      Module(_)            => write!(f, "module"),
      Struct(ref name, ..) => write!(f, "{}", name),

      Func(ref params, ref return_type, ..) => {
        write!(f, "fun(")?;

        for (index, element) in params.iter().enumerate() {
          if index < params.len() - 1 {
            write!(f, "{}, ", element)?
          } else {
            write!(f, "{}", element)?
          }
        }

        write!(f, ") -> {}", return_type)
      },
    }
  }
}



impl PartialEq for TypeMode {
  fn eq(&self, other: &TypeMode) -> bool {
    use self::TypeMode::*;

    match (self, other) {
      (&Regular,    &Regular)     => true,
      (&Regular,    &Immutable)   => true,
      (&Immutable,  &Immutable)   => true,
      (&Immutable,  &Regular)     => true,
      (_,           &Optional)    => true,
      (&Optional,   _)            => true,
      (&Undeclared, _)            => false,
      (_,           &Undeclared)  => false,
      (&Splat(a),      &Splat(b)) => &a == &b,
      (&Unwrap(_),  _)            => true,
      (_,           &Unwrap(_))   => true,
      _                           => false,
    }
  }
}

impl Display for TypeMode {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    use self::TypeMode::*;

    match *self {
      Regular     => Ok(()),
      Immutable   => write!(f, "constant "),
      Undeclared  => write!(f, "undeclared "),
      Optional    => write!(f, "optional "),
      Implemented => Ok(()),
      Splat(_)    => write!(f, ".."),
      Unwrap(_)   => write!(f, "*"),
    }
  }
}



#[derive(Debug, Clone, PartialEq)]
pub struct Type {
  pub node: TypeNode,
  pub mode: TypeMode,
}

impl Type {
  pub fn new(node: TypeNode, mode: TypeMode) -> Self {
    Self {
      node, mode,
    }
  }



  pub fn is_method(&self) -> bool {
    if let TypeNode::Func(.., is_method) = self.node {
      return is_method
    }

    false
  }



  pub fn id(id: Rc<Expression>) -> Self {
    Type::new(TypeNode::Id(id), TypeMode::Regular)
  }

  pub fn from(node: TypeNode) -> Type {
    Type::new(node, TypeMode::Regular)
  }

  pub fn array(t: Type, len: Option<usize>) -> Type {
    Type::new(TypeNode::Array(Rc::new(t), len), TypeMode::Regular)
  }

  pub fn function(params: Vec<Type>, return_type: Type, is_method: bool) -> Self {
    Type::new(TypeNode::Func(params, Rc::new(return_type), None, is_method), TypeMode::Regular)
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "{}{}", self.mode, self.node)
  }
}



#[derive(Debug, Clone)]
pub enum FlagContext {
  Block(Option<Type>),
  Nothing,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Inside {
  Loop,
  Calling(Pos),
  Splat(Option<usize>),
  Implement(Type),
  Function,
  Nothing,
}


#[derive(Clone)]
pub struct ImplementationFrame {
  pub implementations: HashMap<String, HashMap<String, Type>>,
}

impl ImplementationFrame {
  pub fn new() -> Self {
    Self {
      implementations: HashMap::new()
    }
  }
}



pub struct Visitor<'v> {
  pub symtab: SymTab,

  pub source: &'v Source,
  pub ast:    &'v Vec<Statement>,
  
  pub flag:   Option<FlagContext>,
  pub inside: Vec<Inside>,

  pub method_calls: HashMap<Pos, bool>,
}

impl<'v> Visitor<'v> {
  pub fn visit(&mut self) -> Result<(), ()> {
    self.visit_block(self.ast, false)?;

    Ok(())
  }



  pub fn new(ast: &'v Vec<Statement>, source: &'v Source) -> Self {
    Visitor {
      symtab: SymTab::new(),

      source,
      ast,

      flag:   None,
      inside: Vec::new(),

      method_calls: HashMap::new(),
    }
  }



  fn visit_statement(&mut self, statement: &Statement) -> Result<(), ()> {
    use self::StatementNode::*;

    match statement.node {
      Expression(ref expr) => self.visit_expression(expr),
      Variable(..)         => self.visit_variable(&statement.node, &statement.pos),
    
      Assignment(ref left, ref right) => {
        self.visit_expression(left)?;
        self.visit_expression(right)?;

        let a = self.type_expression(left)?;
        let b = self.type_expression(right)?;

        self.assert_types(a, b, &left.pos)?;

        Ok(())
      },

      _ => Ok(())
    }
  }

  fn visit_expression(&mut self, expression: &Expression) -> Result<(), ()> {
    Ok(())
  }

  fn visit_variable(&mut self, variable: &StatementNode, pos: &Pos) -> Result<(), ()> {
    use self::ExpressionNode::*;

     if let &StatementNode::Variable(ref var_type, ref name, ref right) = variable {
      let mut variable_type = var_type.clone();

      if let TypeNode::Id(ref ident) = var_type.node {
        let ident_type = self.type_expression(&ident)?;

        if let TypeNode::Struct(..) = ident_type.node {
          variable_type = Type::from(ident_type.node)
        } else {
          return Err(
            response!(
              Wrong(format!("can't use `{}` as type", ident_type)),
              self.source.file,
              ident.pos
            )
          )
        }
      }

      variable_type = Type::from(variable_type.node.clone());

      self.assign(name.to_owned(), variable_type.clone());

      if let &Some(ref right) = right {
        match right.node {
          Function(..) | Block(_) | If(..) | While(..) => (),
          _ => self.visit_expression(right)?,
        }

        let right_type = self.type_expression(&right)?;

        if variable_type.node != TypeNode::Nil {
          if !variable_type.node.check_expression(&Parser::fold_expression(right)?.node) && variable_type.node != right_type.node {
            return Err(
              response!(
                Wrong(format!("mismatched types, expected type `{}` got `{}`", variable_type.node, right_type)),
                self.source.file,
                right.pos
              )
            )
          } else {
            self.assign(name.to_owned(), variable_type.to_owned())
          }

        } else {
          self.assign(name.to_owned(), right_type)
        }

        match right.node {
          Function(..) | Block(_) | If(..) | While(..) => self.visit_expression(right)?,
          _ => (),
        }

      } else {
        self.assign(name.to_owned(), variable_type.to_owned())
      }

      Ok(())
    } else {
      unreachable!()
    }
  }



  pub fn type_statement(&mut self, statement: &Statement) -> Result<Type, ()> {
    use self::StatementNode::*;

    let t = match statement.node {
      Expression(ref expression) => self.type_expression(expression)?,
      Return(ref expression)     => if let Some(ref expression) = *expression {
        self.type_expression(expression)?
      } else {
        Type::from(TypeNode::Nil)
      }
      _ => Type::from(TypeNode::Nil)
    };

    Ok(t)
  }

  fn type_expression(&mut self, expression: &Expression) -> Result<Type, ()> {
    use self::ExpressionNode::*;

    let t = match expression.node {
      Str(_)   => Type::from(TypeNode::Str),
      Char(_)  => Type::from(TypeNode::Char),
      Bool(_)  => Type::from(TypeNode::Bool),
      Int(_)   => Type::from(TypeNode::Int(32)),
      Float(_) => Type::from(TypeNode::Float(32)),

      Array(ref content)  => Type::array(self.type_expression(content.first().unwrap())?, Some(content.len())),

      Function(ref params, ref return_type, _, is_method) => {
        let mut param_types = Vec::new();

        for param in params {
          param_types.push(param.1.clone())
        }

        Type::from(TypeNode::Func(param_types, Rc::new(return_type.clone()), Some(Rc::new(expression.node.clone())), is_method))
      },

      Block(ref statements) => {
        let flag_backup = self.flag.clone();

        if self.flag.is_none() {
          self.flag = Some(FlagContext::Block(None))
        }

        let block_type = if statements.len() > 0 {
          for element in statements {

            match element.node {
              StatementNode::Expression(ref expression) => match expression.node {
                Block(_) | If(..) | While(..) => { self.type_expression(expression)?; },

                _ => (),
              },

              StatementNode::Return(ref return_type) => {
                let flag = self.flag.clone();

                if let Some(ref flag) = flag {
                  if let &FlagContext::Block(ref consistent) = flag {

                    let return_type = if let Some(ref return_type) = *return_type {
                      self.type_expression(&return_type)?
                    } else {
                      Type::from(TypeNode::Nil)
                    };

                    if let Some(ref consistent) = *consistent {
                      if return_type != *consistent {
                        return Err(
                          response!(
                            Wrong(format!("mismatched types, expected `{}` found `{}`", consistent, return_type)),
                            self.source.file,
                            expression.pos
                          )
                        )
                      }
                    } else {
                      self.flag = Some(FlagContext::Block(Some(return_type.clone())))
                    }
                  }
                }
              },

              _ => (),
            }
          }

          self.visit_expression(&expression)?;

          self.symtab.revert_frame();

          let last          = statements.last().unwrap();
          let implicit_type = self.type_statement(last)?;

          self.pop_scope();

          if let Some(flag) = self.flag.clone() {
            if let FlagContext::Block(ref consistent) = flag {
              if let Some(ref consistent) = *consistent {
                if implicit_type.node != consistent.node {
                  return Err(
                    response!(
                      Wrong(format!("mismatched types, expected `{}` found `{}`", consistent, implicit_type)),
                      self.source.file,
                      last.pos
                    )
                  )
                }
              } else {
                self.flag = Some(FlagContext::Block(Some(implicit_type.clone())))
              }
            }
          }

          implicit_type

        } else {
          Type::from(TypeNode::Nil)
        };

        self.flag = flag_backup;

        block_type
      },

      Cast(_, ref t) => t.to_owned(),

      _ => Type::from(TypeNode::Nil)
    };

    Ok(t)
  }



  // `ensure_implicit` gets mad at wannabe implicit returns
  fn visit_block(&mut self, content: &Vec<Statement>, ensure_implicits: bool) -> Result<(), ()> {
    for (i, statement) in content.iter().enumerate() {
      // ommiting functions, for that extra user-feel
      if let StatementNode::Variable(_, ref name, ref value) = statement.node {
        if let Some(ref right) = *value {
          if let ExpressionNode::Function(ref params, ref retty, .., is_method) = right.node {

            let mut types = params.iter().map(|x| x.1.clone()).collect::<Vec<Type>>();

            let t = Type::from(
              TypeNode::Func(types, Rc::new(retty.clone()), Some(Rc::new(right.node.clone())), is_method)
            );

            self.assign(name.to_owned(), t);

            continue
          }
        }
      }

      if ensure_implicits {
        if i < content.len() - 1 {
          if let StatementNode::Expression(ref expression) = statement.node {
            self.ensure_no_implicit(expression)?
          }
        }
      }

      self.visit_statement(&statement)?
    }

    Ok(())
  }



  fn ensure_no_implicit(&self, expression: &Expression) -> Result<(), ()> {
    use self::ExpressionNode::*;

    match expression.node {
      Block(ref statements) => if let Some(statement) = statements.last() {
        if let StatementNode::Expression(ref expression) = statement.node {
          match expression.node {

            Call(..)   => (),
            Block(..)  => { self.ensure_no_implicit(expression)?; }

            If(_, ref expr, _) | While(_, ref expr) => self.ensure_no_implicit(&*expr)?,

            _ => return Err(
              response!(
                Wrong("unexpected expression without context"),
                self.source.file,
                expression.pos
              )
            )
          }
        }

        ()
      } else {
        ()
      },

      Call(..) => (),

      If(_, ref expr, _) | While(_, ref expr) => self.ensure_no_implicit(&*expr)?,

      _ => return Err(
        response!(
          Wrong("unexpected expression without context"),
          self.source.file,
          expression.pos
        )
      )
    }

    Ok(())
  }



  fn assert_types(&self, a: Type, b: Type, pos: &Pos) -> Result<bool, ()> {
    if a != b {
      Err(
        response!(
          Wrong(format!("mismatched types, expected `{}` got `{}`", a, b)),
          self.source.file,
          pos
        )
      )
    } else {
      Ok(true)
    }
  }


  fn fetch(&self, name: &String, pos: &Pos) -> Result<Type, ()> {
    if let Some(t) = self.symtab.fetch(name) {
      Ok(t)
    } else {
      Err(
        response!(
          Wrong(format!("can't seem to find `{}`", name)),
          self.source.file,
          pos
        )
      )
    }
  }

  fn fetch_str(&self, name: &str, pos: &Pos) -> Result<Type, ()> {
    if let Some(t) = self.symtab.fetch_str(name) {
      Ok(t)
    } else {
      Err(
        response!(
          Wrong(format!("can't seem to find `{}`", name)),
          self.source.file,
          pos
        )
      )
    }
  }

  
  fn assign_str(&mut self, name: &str, t: Type) {
    self.symtab.assign_str(name, t)
  }

  fn assign(&mut self, name: String, t: Type) {
    self.symtab.assign(name, t)
  }


  
  fn push_scope(&mut self) {
    self.symtab.push()
  }

  fn pop_scope(&mut self) {
    self.symtab.pop()
  }
}