#include "seahorn/seahorn.h"
extern int nd();

int main() {
  int x = nd(), y = nd();
  *(x >= y ? &x : &y) += 1;
  sassert(x != y + 1);
  return 0;
}
