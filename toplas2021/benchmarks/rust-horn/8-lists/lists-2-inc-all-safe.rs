fn rand<T>() -> T { loop {} }

enum List<T> {
  Cons(T, Box<List<T>>),
  Nil,
}
use List::*;

fn inc<'a>(mla: &'a mut List<i32>) {
  match mla {
    Cons(ma, mla2) => {
      *ma += 1;
      inc(mla2);
    }
    Nil => {}
  }
}
fn sum(la: &List<i32>) -> i32 {
  match la {
    Cons(a, la2) => a + sum(la2),
    Nil => 0,
  }
}
fn length(la: &List<i32>) -> i32 {
  match la {
    Cons(a, la2) => 1 + length(la2),
    Nil => 0,
  }
}
fn main() {
  let mut la = rand::<List<i32>>();
  let n = sum(&la);
  let l = length(&la);
  inc(&mut la);
  let r = sum(&la);
  assert!(r == n + l);
}
