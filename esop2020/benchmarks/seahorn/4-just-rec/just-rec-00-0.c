#include "seahorn/seahorn.h"

extern int nd();

void just_rec(int *pa) {
  if (nd()) return;
  int b = nd();
  just_rec(&b);
}

int main() {
  int a = nd();
  int old_a = a;
  just_rec(&a);
  sassert(old_a == a);
}
