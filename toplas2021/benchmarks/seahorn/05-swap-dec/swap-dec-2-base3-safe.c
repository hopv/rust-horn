#include "seahorn/seahorn.h"
extern int nd();

void may_swap(int **mma, int **mmb) {
  if (nd()) {
    int *tmp = *mma;
    *mma = *mmb;
    *mmb = tmp;
  }
}
void swap_dec_three(int **mma, int **mmb, int **mmc) {
  may_swap(mma, mmb);
  may_swap(mmb, mmc);
  may_swap(mma, mmb);
  if (nd()) return;
  **mma -= 1;
  **mmb -= 2;
  **mmc -= 3;
  swap_dec_three(mma, mmb, mmc);
}
int main() {
  int a = nd(), b = nd(), c = nd();
  int a0 = a;
  int *ma = &a, *mb = &b, *mc = &c;
  swap_dec_three(&ma, &mb, &mc);
  sassert(a0 >= a);
  return 0;
}
