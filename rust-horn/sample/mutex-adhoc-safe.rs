struct Mutex;

impl Mutex {
    fn new(_x: i32) -> Mutex {
        println!("Creating mutex");
        Mutex
    }
    fn lock(&mut self) -> &mut i32 {
        println!("Locking mutex");
        unimplemented!()
    }
    fn clone(&mut self) -> Mutex {
        println!("Cloning mutex");
        Mutex
    }
    fn drop(self) {
        println!("Dropping mutex");
    }
}

fn rand() -> i32 { 0 }

fn main() {
    let x = rand();
    let mut m = Mutex::new(x);
    let mut m2 = m.clone();
    let mut m3 = m2.clone();
    let lock = m.lock();
    *lock = *lock + 1;
    m.drop();
    let lock = m2.lock();
    *lock = *lock + 2;
    m2.drop();
    assert!(*m3.lock() >= x);
}
