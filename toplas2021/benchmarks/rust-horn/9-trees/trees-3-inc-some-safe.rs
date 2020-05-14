fn rand<T>() -> T { loop {} }

enum Tree<T> {
  Node(Box<Tree<T>>, T, Box<Tree<T>>),
  Leaf,
}
use Tree::*;

fn take_some<'a>(mta: &'a mut Tree<i32>) -> &'a mut i32 {
  match mta {
    Node(mtal, ma, mtar) => {
      if rand() {
        ma
      } else if rand() {
        take_some(mtal)
      } else {
        take_some(mtar)
      }
    }
    Leaf => take_some(mta),
  }
}
fn sum(ta: &Tree<i32>) -> i32 {
  match ta {
    Node(tal, x, tar) => sum(tal) + x + sum(tar),
    Leaf => 0,
  }
}
fn main() {
  let mut ta = rand::<Tree<i32>>();
  let n = sum(&ta);
  let mb = take_some(&mut ta);
  *mb += 1;
  let r = sum(&ta);
  assert!(r == n + 1);
}
