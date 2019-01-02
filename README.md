# Boss

Boss is a gradually-typed programming with unreasonably many primitive types for a high-level language. It has structs, Rust-like implementations and runs on a low-end virtual machine.

The syntax looks basically like this:

```
Vector: struct {
  x: f32
  y: f32
}

implement Vector {
  len: fun(self) -> f32 {
    (self x^2 + self y^2)^0.5
  }
}

pos := new Vector {
  x: 10
  y: 10
}

printf("the length is {}", pos len())
```
