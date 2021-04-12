pub fn rand<T>() -> T { unimplemented!() }

fn just_rec(ma: &mut i32) {
  if rand() {
    return;
  }
  let mut b = rand();
  just_rec(&mut b);
}
fn main() {
  let mut a = rand();
  let old_a = a;
  just_rec(&mut a);
  assert!(old_a == a);
}
