pub fn rand<T>() -> T { unimplemented!() }

fn linger_dec(ma: &mut i32) {
  *ma -= 1;
  if rand() {
    return;
  }
  let mut x = rand();
  linger_dec(if rand() { &mut x } else { ma });
}
fn main() {
  let mut a = rand();
  let old_a = a;
  linger_dec(&mut a);
  assert!(old_a > a);
}
