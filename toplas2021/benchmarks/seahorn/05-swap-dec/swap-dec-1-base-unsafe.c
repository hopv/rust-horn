#include "seahorn/seahorn.h"
extern int nd();

void may_swap(int **mma, int **mmb) {
  if (nd()) {
    int *tmp = *mma;
    *mma = *mmb;
    *mmb = tmp;
  }
}
void swap_dec(int **mma, int **mmb) {
  may_swap(mma, mmb);
  if (nd()) return;
  **mma -= 1;
  **mmb -= 2;
  swap_dec(mma, mmb);
}
int main() {
  int a = nd(), b = nd();
  int a0 = a;
  int *ma = &a, *mb = &b;
  swap_dec(&ma, &mb);
  sassert(a0 >= a && a0 - a <= 3);
  return 0;
}
