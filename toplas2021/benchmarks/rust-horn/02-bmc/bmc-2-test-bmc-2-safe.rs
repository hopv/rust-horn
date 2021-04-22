fn rand<T>() -> T { unimplemented!() }

fn main() {
  let mut x = 1;
  let mut y = 1;
  while rand() {
    if rand() {
      x += 1;
      y += 1;
    }
    if rand() {
      x += 1;
    }
  }
  assert!(x >= y);
}
