fn rand<T>() -> T { loop {} }

enum Tree<T> {
  Node(Box<Tree<T>>, T, Box<Tree<T>>),
  Leaf,
}
use Tree::*;

fn inc<'a>(mta: &'a mut Tree<i32>) {
  match mta {
    Node(mtal, mx, mtar) => {
      inc(mtal);
      *mx += 1;
      inc(mtar);
    }
    Leaf => {}
  }
}
fn sum(ta: &Tree<i32>) -> i32 {
  match ta {
    Node(tal, a, tar) => sum(tal) + a + sum(tar),
    Leaf => 0,
  }
}
fn size(ta: &Tree<i32>) -> i32 {
  match ta {
    Node(tal, _, tar) => size(tal) + 1 + size(tar),
    Leaf => 0,
  }
}
fn main() {
  let mut ta = rand::<Tree<i32>>();
  let n = sum(&ta);
  let s = size(&ta);
  inc(&mut ta);
  let r = sum(&ta);
  assert!(r > n + s);
}
