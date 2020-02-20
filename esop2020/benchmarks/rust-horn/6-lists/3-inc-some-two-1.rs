pub fn rand<T>() -> T { loop {} }

enum List {
  Cons(i32, Box<List>),
  Nil,
}
use List::*;
fn take_some_rest<'a>(mxs: &'a mut List) -> (&'a mut i32, &'a mut List) {
  match mxs {
    Cons(mx, mxs2) => {
      if rand() {
        (mx, mxs2)
      } else {
        take_some_rest(mxs2)
      }
    }
    Nil => take_some_rest(mxs),
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
  let (my, mxs2) = take_some_rest(&mut xs);
  let (mz, _) = take_some_rest(mxs2);
  *my += 1;
  *mz += 1;
  let r = sum(&xs);
  assert!(r > n + 2);
}
