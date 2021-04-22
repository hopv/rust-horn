#include "seahorn/seahorn.h"
extern int nd();

typedef struct T {
  int val;
} T;

int main() {
  T x = {11};
  T y = {22};

  T *z = nd() ? &x : &y;

  z->val += 33;
  // here `z` dies and the permission should "go back" to `x` or `y`
  x.val += 44;
  y.val += 44;

  sassert(x.val == 88 || x.val == 55);
  sassert(y.val == 66 || y.val == 99);

  return 0;
}
