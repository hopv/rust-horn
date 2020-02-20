pub fn rand<T>() -> T { loop {} }

fn linger_dec_bound(n: i32, ma: &mut i32) {
  if n == 0 {
    return;
  }
  *ma -= 1;
  let mut x = rand();
  linger_dec_bound(n - 1, if rand() { &mut x } else { ma });
}
fn main() {
  let n = rand();
  let mut a = rand();
  let old_a = a;
  linger_dec_bound(n, &mut a);
  assert!(old_a >= a && old_a - a <= n);
}
