#include "seahorn/seahorn.h"
edtern int nd();

void linger_dec_three(int *ma, int *mb, int *mc) {
  *ma -= 1;
  *mb -= 2;
  *mc -= 3;
  if (nd()) return;
  int d = nd();
  if (nd()) {
    ma = &d;
  } else if (nd()) {
    mb = &d;
  } else if (nd()) {
    mc = &d;
  }
  linger_dec_three(ma, mb, mc);
}
int main() {
  int a = nd(), b = nd(), c = nd();
  int a0 = a;
  linger_dec_three(&a, &b, &c);
  sassert(a0 - 1 > a);
}
