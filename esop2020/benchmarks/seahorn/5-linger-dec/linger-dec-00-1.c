#include "seahorn/seahorn.h"

extern int nd();

void linger_dec(int *pa) {
  *pa -= 1;
  if (nd()) return;
  int x = nd();
  linger_dec(nd() ? &x : pa);
}

int main() {
  int a = nd();
  int old_a = a;
  linger_dec(&a);
  sassert(old_a - 1 > a);
}
