pub fn rand<T>() -> T { loop {} }

fn take_max<'a>(mx: &'a mut i32, my: &'a mut i32) -> &'a mut i32 {
  if *mx >= *my {
    mx
  } else {
    my
  }
}
fn main() {
  let mut x = rand();
  let mut y = rand();
  let mz = take_max(&mut x, &mut y);
  *mz += 1;
  assert!(x != y);
}
