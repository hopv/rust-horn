pub fn rand<T>() -> T { loop {} }

fn take_max<'a>(mx: &'a mut i32, my: &'a mut i32) -> &'a mut i32 {
  if *mx >= *my {
    mx
  } else {
    my
  }
}
fn inc_max_repeat(n: i32, mx: &mut i32, my: &mut i32) {
  if n == 0 {
    return;
  }
  let mz = take_max(mx, my);
  *mz += 1;
  inc_max_repeat(n - 1, mx, my);
}
fn main() {
  let n = rand();
  let mut x = rand();
  let mut y = rand();
  inc_max_repeat(n, &mut x, &mut y);
  assert!(x - y > n || y - x > n);
}
