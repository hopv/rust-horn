fn rand<T>() -> T { loop {} }

enum List<T> {
  Cons(T, Box<List<T>>),
  Nil,
}
use List::*;

fn take_some<'a>(mla: &'a mut List<i32>) -> &'a mut i32 {
  match mla {
    Cons(ma, mla2) => {
      if rand() {
        ma
      } else {
        take_some(mla2)
      }
    }
    Nil => take_some(mla),
  }
}
fn sum(la: &List<i32>) -> i32 {
  match la {
    Cons(x, la2) => x + sum(la2),
    Nil => 0,
  }
}
fn main() {
  let mut la = rand::<List<i32>>();
  let n = sum(&la);
  let mb = take_some(&mut la);
  *mb += 1;
  let r = sum(&la);
  assert!(r > n + 1);
}
