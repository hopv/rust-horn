struct Sender;

impl Sender {
    fn send(&mut self, value: i32) {
        println!("Sending value: {}", value);
    }
    fn clone(&mut self) -> Self {
        println!("Cloning sender");
        Sender
    }
    fn drop(self) {
        println!("Dropping sender");
    }
}

struct Receiver;

impl Receiver {
    fn recv(&mut self) -> i32 {
        println!("Receiving value");
        0
    }
}

fn channel() -> (Sender, Receiver) { (Sender, Receiver) }

fn main() {
    let (mut sender, mut receiver) = channel();
    let mut sender2 = sender.clone();
    sender.send(1);
    sender2.send(2);
    sender.drop();
    sender2.drop();
    let received = receiver.recv();
    let received_2 = receiver.recv();
    assert!(received_2 == 1);
}
