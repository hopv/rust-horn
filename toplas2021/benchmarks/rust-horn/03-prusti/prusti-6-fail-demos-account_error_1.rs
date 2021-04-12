fn rand<T>() -> T { unimplemented!() }

struct Account {
  bal: u32,
}

impl Account {
  fn balance(&self) -> u32 { self.bal }
  fn deposit(&mut self, amount: u32) { self.bal = self.bal + amount; }
  fn withdraw(&mut self, amount: u32) { self.bal = self.bal - amount; }
}

fn main() {
  let mut acc: Account = rand();
  let mut acc2: Account = rand();
  let amount = rand();
  let acc_old_balance = acc.balance();
  acc.withdraw(amount);
  acc2.deposit(amount);
  assert!(acc.balance() == acc_old_balance + amount);
}
