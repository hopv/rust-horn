fn rand<T>() -> T { loop {} }

enum List<T> {
  Cons(T, Box<List<T>>),
  Nil,
}
use List::*;

fn append<'a>(mla: &'a mut List<i32>, lb: List<i32>) {
  match mla {
    Cons(_, mla2) => append(mla2, lb),
    Nil => *mla = lb,
  }
}
fn sum(la: &List<i32>) -> i32 {
  match la {
    Cons(a, la2) => a + sum(la2),
    Nil => 0,
  }
}
fn main() {
  let mut la = rand::<List<i32>>();
  let lb = rand::<List<i32>>();
  let m = sum(&la);
  let n = sum(&lb);
  append(&mut la, lb);
  let r = sum(&la);
  assert!(r > m + n);
}
