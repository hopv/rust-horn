#include "seahorn/seahorn.h"
extern int nd();

void linger_dec_bound_three(int n, int *ma, int *mb, int *mc) {
  if (n == 0) return;
  *ma -= 1;
  *mb -= 2;
  *mc -= 3;
  int d = nd();
  if (nd()) {
    ma = &d;
  } else if (nd()) {
    mb = &d;
  } else if (nd()) {
    mc = &d;
  }
  linger_dec_bound_three(n - 1, ma, mb, mc);
}
int main() {
  int n = nd(), a = nd(), b = nd(), c = nd();
  int a0 = a;
  linger_dec_bound_three(n, &a, &b, &c);
  sassert(a0 >= a && a0 - a <= 3 * n);
}
