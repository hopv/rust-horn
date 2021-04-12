pub fn rand<T>() -> T { unimplemented!() }

fn linger_dec_bound_three(n: i32, ma: &mut i32, mb: &mut i32, mc: &mut i32) {
  if n == 0 {
    return;
  }
  *ma -= 1;
  *mb -= 2;
  *mc -= 3;
  let mut x = rand();
  let mut new_ma = ma;
  let mut new_mb = mb;
  let mut new_mc = mc;
  if rand() {
    new_ma = &mut x;
  } else if rand() {
    new_mb = &mut x;
  } else if rand() {
    new_mc = &mut x;
  }
  linger_dec_bound_three(n - 1, new_ma, new_mb, new_mc);
}
fn main() {
  let n = rand();
  let mut a = rand();
  let mut b = rand();
  let mut c = rand();
  let old_a = a;
  linger_dec_bound_three(n, &mut a, &mut b, &mut c);
  assert!(old_a >= a && old_a - a < 3 * n);
}
