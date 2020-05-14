#include "seahorn/seahorn.h"

extern int nd();

void may_swap(int **ppx, int **ppy) {
  if (nd()) {
    int *tmp = *ppx;
    *ppx = *ppy;
    *ppy = tmp;
  }
}
void swap_dec(int **ppa, int **ppb) {
  may_swap(ppa, ppb);
  if (nd()) return;
  **ppa -= 1;
  **ppb -= 2;
  swap_dec(ppa, ppb);
}
int main() {
  int x = nd(), y = nd();
  int old_x = x;
  int *pa = &x, *pb = &y;
  swap_dec(&pa, &pb);
  sassert(old_x >= x);
  return 0;
}
