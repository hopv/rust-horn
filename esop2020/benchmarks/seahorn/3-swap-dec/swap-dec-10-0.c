#include "seahorn/seahorn.h"

extern int nd();

void may_swap(int **ppx, int **ppy) {
  if (nd()) {
    int *tmp = *ppx;
    *ppx = *ppy;
    *ppy = tmp;
  }
}
void swap_dec_bound(int n, int **ppa, int **ppb) {
  may_swap(ppa, ppb);
  if (n == 0) return;
  **ppa -= 1;
  **ppb -= 2;
  swap_dec_bound(n - 1, ppa, ppb);
}
int main() {
  int n = nd(), x = nd(), y = nd();
  int old_x = x;
  int *pa = &x, *pb = &y;
  swap_dec_bound(n, &pa, &pb);
  sassert(old_x >= x && old_x - x <= 2 * n);
  return 0;
}
