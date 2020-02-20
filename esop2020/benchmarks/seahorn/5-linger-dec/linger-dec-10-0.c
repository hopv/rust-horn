#include "seahorn/seahorn.h"

extern int nd();

void linger_dec_bound(int n, int *pa) {
  if (n == 0) return;
  *pa -= 1;
  int x = nd();
  linger_dec_bound(n - 1, nd() ? &x : pa);
}

int main() {
  int n = nd(), a = nd();
  int old_a = a;
  linger_dec_bound(n, &a);
  sassert(old_a >= a && old_a - a <= n);
}
