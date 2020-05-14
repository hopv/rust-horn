pub fn rand<T>() -> T { loop {} }

enum List {
  Cons(i32, Box<List>),
  Nil,
}
use List::*;
fn append<'a>(mxs: &'a mut List, my: List) {
  match mxs {
    Cons(_, mxs2) => append(mxs2, my),
    Nil => *mxs = my,
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
  let ys = rand::<List>();
  let m = sum(&xs);
  let n = sum(&ys);
  append(&mut xs, ys);
  let r = sum(&xs);
  assert!(r == m + n);
}
