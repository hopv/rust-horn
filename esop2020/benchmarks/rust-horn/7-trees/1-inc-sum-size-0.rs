pub fn rand<T>() -> T { loop {} }

enum Tree {
  Node(Box<Tree>, i32, Box<Tree>),
  Leaf,
}
use Tree::*;
fn inc<'a>(mxs: &'a mut Tree) {
  match mxs {
    Node(mxsl, mx, mxsr) => {
      inc(mxsl);
      *mx += 1;
      inc(mxsr);
    }
    Leaf => {}
  }
}
fn sum(xs: &Tree) -> i32 {
  match xs {
    Node(xsl, x, xsr) => sum(xsl) + x + sum(xsr),
    Leaf => 0,
  }
}
fn size(xs: &Tree) -> i32 {
  match xs {
    Node(xsl, x, xsr) => size(xsl) + 1 + size(xsr),
    Leaf => 0,
  }
}
fn main() {
  let mut xs = rand::<Tree>();
  let n = sum(&xs);
  let s = size(&xs);
  inc(&mut xs);
  let r = sum(&xs);
  assert!(r == n + s);
}
