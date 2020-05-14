fn rand<T>() -> T { loop {} }
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
  let mut a = rand();
  let mut b = rand();
  let mut c = rand();
  let a0 = a;
  let mut ma = &mut a;
  let mut mb = &mut b;
  let mut mc = &mut c;
  swap_dec_three(&mut ma, &mut mb, &mut mc);
  assert!(a0 >= a && a0 - a <= 3);
}
