pub fn rand<T>() -> T { unimplemented!() }

enum Tree {
  Node(Box<Tree>, i32, Box<Tree>),
  Leaf,
}
use Tree::*;
fn some<'a>(mxs: &'a mut Tree) -> &'a mut i32 {
  match mxs {
    Node(mxsl, mx, mxsr) => {
      if rand() {
        mx
      } else if rand() {
        some(mxsl)
      } else {
        some(mxsr)
      }
    }
    Leaf => some(mxs),
  }
}
fn sum(xs: &Tree) -> i32 {
  match xs {
    Node(xsl, x, xsr) => sum(xsl) + x + sum(xsr),
    Leaf => 0,
  }
}
fn main() {
  let mut xs = rand::<Tree>();
  let n = sum(&xs);
  let my = some(&mut xs);
  *my += 1;
  let r = sum(&xs);
  assert!(r == n + 1);
}
