#include "seahorn/seahorn.h"

extern int nd();

void linger_dec_bound_three(int n, int *pa, int *pb, int *pc) {
  if (n == 0) return;
  *pa -= 1;
  *pb -= 2;
  *pc -= 3;
  int x = nd();
  if (nd()) {
    pa = &x;
  } else if (nd()) {
    pb = &x;
  } else if (nd()) {
    pc = &x;
  }
  linger_dec_bound_three(n - 1, pa, pb, pc);
}

int main() {
  int n = nd(), a = nd(), b = nd(), c = nd();
  int old_a = a;
  linger_dec_bound_three(n, &a, &b, &c);
  sassert(old_a >= a && old_a - a < 3 * n);
}
