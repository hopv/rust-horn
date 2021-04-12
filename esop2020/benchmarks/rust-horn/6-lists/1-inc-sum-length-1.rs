pub fn rand<T>() -> T { unimplemented!() }

enum List {
  Cons(i32, Box<List>),
  Nil,
}
use List::*;
fn inc<'a>(mxs: &'a mut List) {
  match mxs {
    Cons(mx, mxs2) => {
      *mx += 1;
      inc(mxs2);
    }
    Nil => {}
  }
}
fn sum(xs: &List) -> i32 {
  match xs {
    Cons(x, xs2) => x + sum(xs2),
    Nil => 0,
  }
}
fn length(xs: &List) -> i32 {
  match xs {
    Cons(x, xs2) => 1 + length(xs2),
    Nil => 0,
  }
}
fn main() {
  let mut xs = rand::<List>();
  let n = sum(&xs);
  let l = length(&xs);
  inc(&mut xs);
  let r = sum(&xs);
  assert!(r > n + l);
}
