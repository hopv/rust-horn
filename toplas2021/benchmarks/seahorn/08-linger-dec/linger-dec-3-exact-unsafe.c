#include "seahorn/seahorn.h"
extern int nd();

void linger_dec_bound(int n, int *ma) {
  if (n == 0) return;
  *ma -= 1;
  int b = nd();
  linger_dec_bound(n - 1, nd() ? &b : ma);
}
int main() {
  int n = nd(), a = nd();
  int a0 = a;
  linger_dec_bound(n, &a);
  sassert(a0 >= a && a0 - a < n);
}
