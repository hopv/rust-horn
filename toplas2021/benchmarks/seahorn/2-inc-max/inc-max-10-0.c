#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

void inc_max_repeat(int n, int *px, int *py) {
  if (n > 0) {
    *(*px >= *py ? px : py) += 1;
    inc_max_repeat(n - 1, px, py);
  }
}
int main() {
  int n = nd(), x = nd(), y = nd();
  inc_max_repeat(n, &x, &y);
  sassert(x - y >= n || y - x >= n);
  return 0;
}
