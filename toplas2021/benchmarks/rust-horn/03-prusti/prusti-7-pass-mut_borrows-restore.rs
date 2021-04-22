fn rand<T>() -> T { unimplemented!() }

struct T {
  val: i32,
}

fn main() {
  let mut x = T { val: 11 };
  let mut y = T { val: 22 };

  let z = if rand() { &mut x } else { &mut y };

  z.val += 33;
  // here `z` dies and the permission should "go back" to `x` or `y`
  x.val += 44;
  y.val += 44;

  assert!(x.val == 88 || x.val == 55);
  assert!(y.val == 66 || y.val == 99);
}
