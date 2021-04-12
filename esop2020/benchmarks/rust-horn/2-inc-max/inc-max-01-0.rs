pub fn rand<T>() -> T { unimplemented!() }
use std::mem::swap;

fn max_mid<'a>(
  mut mx: &'a mut i32, mut my: &'a mut i32, mut mz: &'a mut i32,
) -> (&'a mut i32, &'a mut i32) {
  if *mx > *my {
    swap(&mut mx, &mut my);
  }
  if *my > *mz {
    swap(&mut my, &mut mz);
  }
  if *mx > *my {
    swap(&mut mx, &mut my);
  }
  (mz, my)
}
fn main() {
  let mut x = rand();
  let mut y = rand();
  let mut z = rand();
  let (ma, mb) = max_mid(&mut x, &mut y, &mut z);
  *ma += 2;
  *mb += 1;
  assert!(x != y);
}
