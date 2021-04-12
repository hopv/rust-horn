pub fn rand<T>() -> T { unimplemented!() }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec<'a>(mma: &mut &'a mut i32, mmb: &mut &'a mut i32) {
  may_swap(mma, mmb);
  if rand() {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  swap_dec(mma, mmb);
}
fn main() {
  let mut x = rand();
  let mut y = rand();
  let old_x = x;
  let mut ma = &mut x;
  let mut mb = &mut y;
  swap_dec(&mut ma, &mut mb);
  assert!(old_x >= x);
}
