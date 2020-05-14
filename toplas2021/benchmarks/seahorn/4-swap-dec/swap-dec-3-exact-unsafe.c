#include "seahorn/seahorn.h"
extern int nd();

void may_swap(int **mma, int **mmb) {
  if (nd()) {
    int *tmp = *mma;
    *mma = *mmb;
    *mmb = tmp;
  }
}
void swap_dec_bound(int n, int **mma, int **mmb) {
  may_swap(mma, mmb);
  if (n == 0) return;
  **mma -= 1;
  **mmb -= 2;
  swap_dec_bound(n - 1, mma, mmb);
}
int main() {
  int n = nd(), a = nd(), b = nd();
  int a0 = a;
  int *ma = &a, *mb = &b;
  swap_dec_bound(n, &ma, &mb);
  sassert(a0 >= a && a0 - a < 2 * n);
  return 0;
}
