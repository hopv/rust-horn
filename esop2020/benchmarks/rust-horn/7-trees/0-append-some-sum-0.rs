pub fn rand<T>() -> T { unimplemented!() }

enum Tree {
  Node(Box<Tree>, i32, Box<Tree>),
  Leaf,
}
use Tree::*;
fn append_some<'a>(mxs: &'a mut Tree, my: Tree) {
  match mxs {
    Node(mxsl, mx, mxsr) => {
      if rand() {
        append_some(mxsl, my)
      } else {
        append_some(mxsr, my)
      }
    }
    Leaf => *mxs = my,
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
  let ys = rand::<Tree>();
  let m = sum(&xs);
  let n = sum(&ys);
  append_some(&mut xs, ys);
  let r = sum(&xs);
  assert!(r == m + n);
}
