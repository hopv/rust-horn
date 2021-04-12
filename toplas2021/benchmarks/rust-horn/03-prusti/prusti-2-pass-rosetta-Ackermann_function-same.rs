fn rand<T>() -> T { unimplemented!() }

fn ack(m: isize, n: isize) -> isize {
  if m == 0 {
    n + 1
  } else if n == 0 {
    ack(m - 1, 1)
  } else {
    ack(m - 1, ack(m, n - 1))
  }
}
fn ack1(m: isize, n: isize) -> isize {
  if m == 0 {
    n + 1
  } else if n == 0 {
    ack1(m - 1, 1)
  } else {
    ack1(m - 1, ack1(m, n - 1))
  }
}

fn main() {
  let m = rand();
  let n = rand();
  if (0 <= m && 0 <= n) {
    assert!(ack(m, n) == ack1(m, n));
  }
}
