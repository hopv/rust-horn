pub fn rand<T>() -> T { loop {} }

enum List {
  Cons(i32, Box<List>),
  Nil,
}
use List::*;
fn take_some<'a>(mxs: &'a mut List) -> &'a mut i32 {
  match mxs {
    Cons(mx, mxs2) => {
      if rand() {
        mx
      } else {
        take_some(mxs2)
      }
    }
    Nil => take_some(mxs),
  }
}
fn sum(xs: &List) -> i32 {
  match xs {
    Cons(x, xs2) => x + sum(xs2),
    Nil => 0,
  }
}
fn main() {
  let mut xs = rand::<List>();
  let n = sum(&xs);
  let my = take_some(&mut xs);
  *my += 1;
  let r = sum(&xs);
  assert!(r == n + 1);
}
