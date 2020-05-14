#include "seahorn/seahorn.h"

extern int nd();

void linger_dec_three(int *pa, int *pb, int *pc) {
  *pa -= 1;
  *pb -= 2;
  *pc -= 3;
  if (nd()) return;
  int x = nd();
  if (nd()) {
    pa = &x;
  } else if (nd()) {
    pb = &x;
  } else if (nd()) {
    pc = &x;
  }
  linger_dec_three(pa, pb, pc);
}

int main() {
  int a = nd(), b = nd(), c = nd();
  int old_a = a;
  linger_dec_three(&a, &b, &c);
  sassert(old_a - 1 > a);
}
