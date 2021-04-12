pub fn rand<T>() -> T { unimplemented!() }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec_bound<'a>(n: i32, mma: &mut &'a mut i32, mmb: &mut &'a mut i32) {
  may_swap(mma, mmb);
  if n == 0 {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  swap_dec_bound(n - 1, mma, mmb);
}
fn main() {
  let n = rand();
  let mut x = rand();
  let mut y = rand();
  let old_x = x;
  let mut ma = &mut x;
  let mut mb = &mut y;
  swap_dec_bound(n, &mut ma, &mut mb);
  assert!(old_x >= x && old_x - x < 2 * n);
}
