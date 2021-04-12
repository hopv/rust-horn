fn rand<T>() -> T { unimplemented!() }

struct Point {
  x: i32,
  y: i32,
}

fn shift_x(p: &mut Point, s: i32) { p.x = p.x + s }

fn main() {
  let mut segm: (Box<Point>, Box<Point>) = rand();
  let endBox = &mut segm.1;
  let endPt = &mut **endBox;
  // segm.1, endBox are not usable here
  let end_x = (*endPt).x;
  shift_x(endPt, (*segm.0).x - end_x);
  // borrows expire: segm.1 usable again
  assert!((*segm.0).x == (*segm.1).x);
}
