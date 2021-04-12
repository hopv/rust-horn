#include "seahorn/seahorn.h"
extern int nd();

void just_rec(int *pa) {
  if (nd()) return;
  int b = nd();
  just_rec(&b);
}
int main() {
  int a = nd();
  int a0 = a;
  just_rec(&a);
  sassert(a0 == a);
}
