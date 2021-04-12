pub fn rand<T>() -> T { unimplemented!() }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec_three<'a>(mma: &mut &'a mut i32, mmb: &mut &'a mut i32, mmc: &mut &'a mut i32) {
  may_swap(mma, mmb);
  may_swap(mmb, mmc);
  may_swap(mma, mmb);
  if rand() {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  **mmc -= 3;
  swap_dec_three(mma, mmb, mmc);
}
fn main() {
  let mut x = rand();
  let mut y = rand();
  let mut z = rand();
  let old_x = x;
  let mut ma = &mut x;
  let mut mb = &mut y;
  let mut mc = &mut z;
  swap_dec_three(&mut ma, &mut mb, &mut mc);
  assert!(old_x >= x)
}
