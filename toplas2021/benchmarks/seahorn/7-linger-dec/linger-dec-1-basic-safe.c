#include "seahorn/seahorn.h"
extern int nd();

void linger_dec(int *ma) {
  *ma -= 1;
  if (nd()) return;
  int a = nd();
  linger_dec(nd() ? &a : ma);
}
int main() {
  int a = nd();
  int a0 = a;
  linger_dec(&a);
  sassert(a0 > a);
}
