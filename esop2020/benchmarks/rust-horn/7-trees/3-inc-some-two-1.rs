pub fn rand<T>() -> T { loop {} }

enum Tree {
  Node(Box<Tree>, i32, Box<Tree>),
  Leaf,
}
use Tree::*;
fn some<'a>(mxs: &'a mut Tree) -> (&'a mut i32, &'a mut Tree) {
  match mxs {
    Node(mxsl, mx, mxsr) => {
      if rand() {
        (mx, if rand() { mxsl } else { mxsr })
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
  let (my, mxs2) = some(&mut xs);
  let (mz, _) = some(mxs2);
  *my += 1;
  *mz += 1;
  let r = sum(&xs);
  assert!(r > n + 2);
}
