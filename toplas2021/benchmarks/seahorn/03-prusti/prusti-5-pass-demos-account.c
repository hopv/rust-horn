#include "seahorn/seahorn.h"
#include <stdlib.h>
extern unsigned nd();

typedef struct Account {
  unsigned bal;
} Account;

unsigned balance(Account *acc) { return acc->bal; }
unsigned deposit(Account *acc, unsigned amount) {
  acc->bal = acc->bal + amount;
}
unsigned withdraw(Account *acc, unsigned amount) {
  acc->bal = acc->bal - amount;
}

int main() {
  Account acc = {nd()}, acc2 = {nd()};
  unsigned amount = nd();
  unsigned acc_old_balance = balance(&acc);
  withdraw(&acc, amount);
  deposit(&acc2, amount);
  sassert(balance(&acc) == acc_old_balance - amount);
  return 0;
}
