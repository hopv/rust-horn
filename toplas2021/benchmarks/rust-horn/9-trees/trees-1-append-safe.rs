fn rand<T>() -> T { loop {} }

enum Tree<T> {
  Node(Box<Tree<T>>, T, Box<Tree<T>>),
  Leaf,
}
use Tree::*;

fn append<'a>(mta: &'a mut Tree<i32>, tb: Tree<i32>) {
  match mta {
    Node(mtal, _, mtar) => {
      if rand() {
        append(mtal, tb)
      } else {
        append(mtar, tb)
      }
    }
    Leaf => {
      *mta = tb;
    }
  }
}
fn sum(ta: &Tree<i32>) -> i32 {
  match ta {
    Node(tal, a, tar) => sum(tal) + a + sum(tar),
    Leaf => 0,
  }
}
fn main() {
  let mut ta = rand::<Tree<i32>>();
  let tb = rand::<Tree<i32>>();
  let m = sum(&ta);
  let n = sum(&tb);
  append(&mut ta, tb);
  let r = sum(&ta);
  assert!(r == m + n);
}
