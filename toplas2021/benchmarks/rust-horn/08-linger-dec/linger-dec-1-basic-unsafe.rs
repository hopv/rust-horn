fn rand<T>() -> T { unimplemented!() }

fn linger_dec(ma: &mut i32) {
  *ma -= 1;
  if rand() {
    return;
  }
  let mut a = rand();
  linger_dec(if rand() { &mut a } else { ma });
}
fn main() {
  let mut a = rand();
  let a0 = a;
  linger_dec(&mut a);
  assert!(a0 - 1 > a);
}
