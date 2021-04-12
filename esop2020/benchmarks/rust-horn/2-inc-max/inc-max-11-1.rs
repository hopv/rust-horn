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
fn inc_max_three_repeat<'a>(n: i32, mx: &'a mut i32, my: &'a mut i32, mz: &'a mut i32) {
  if n == 0 {
    return;
  }
  let (ma, mb) = max_mid(mx, my, mz);
  *ma += 2;
  *mb += 1;
  inc_max_three_repeat(n - 1, mx, my, mz);
}
fn main() {
  let n = rand();
  let mut x = rand();
  let mut y = rand();
  let mut z = rand();
  inc_max_three_repeat(n, &mut x, &mut y, &mut z);
  assert!(x - y > n || y - x > n);
}
