use std::cell::RefCell;
use std::collections::HashMap;

use std::rc::Rc;

use super::visitor::*;



#[derive(Debug, Clone)]
pub struct Frame {
  pub table: RefCell<HashMap<String, Type>>,
  pub depth: usize,
}

impl Frame {
  pub fn new(depth: usize) -> Self {
    Frame {
      table: RefCell::new(HashMap::new()),
      depth,
    }
  }

  pub fn from(table: HashMap<String, Type>, depth: usize) -> Self {
    Frame {
      table: RefCell::new(table),
      depth,
    }
  }

  pub fn get(&self, name: &String) -> Option<Type> {
    if let Some(v) = self.table.borrow().get(name) {
      Some(v.clone())
    } else {
      None
    }
  }

  pub fn assign(&mut self, name: String, t: Type) {
    self.table.borrow_mut().insert(name, t);
  }
}


#[derive(Debug, Clone)]
pub struct SymTab {
  pub stack:  Vec<Frame>, // active frames
  pub record: Vec<Frame>, // popped frames
}

impl SymTab {
  pub fn new() -> Self {
    SymTab {
      stack:  vec!(Frame::new(0)),
      record: Vec::new(),
    }
  }

  pub fn from(table: HashMap<String, Type>) -> Self {
    SymTab {
      stack:  vec!(Frame::from(table, 0)),
      record: Vec::new()
    }
  }



  pub fn assign(&mut self, name: String, t: Type) {
    self.current_frame_mut().assign(name, t)
  }

  pub fn assign_str(&mut self, name: &str, t: Type) {
    self.current_frame_mut().assign(name.to_string(), t)
  }



  pub fn fetch(&self, name: &String) -> Option<Type> {
    let mut offset = 1;

    loop {
      let len = self.stack.len();

      if offset > self.stack.len() - 1 {
        return None
      }

      if let Some(t) = self.stack[len - offset].get(name) {
        return Some(t)
      } else {
        offset += 1;
      }
    }
  }

  pub fn fetch_str(&self, name: &str) -> Option<Type> {
    let mut offset = 0;

    loop {
      let len = self.stack.len();

      if let Some(t) = self.stack[len - offset].get(&name.to_string()) {
        return Some(t)
      } else {
        offset += 1;

        if offset == self.stack.len() {
          return None
        }
      }
    }
  }



  pub fn revert_frame(&mut self) {
    self.stack.push(self.record.last().unwrap().clone());
  }



  pub fn current_frame(&self) -> &Frame {
    self.stack.last().unwrap()
  }

  pub fn current_frame_mut(&mut self) -> &mut Frame {
    self.stack.last_mut().unwrap()
  }



  pub fn push(&mut self) {
    self.stack.push(Frame::new(self.stack.len()))
  }

  pub fn pop(&mut self) {
    let popped = self.stack.pop().unwrap();

    self.record.push(popped)
  }
}