#include "seahorn/seahorn.h"
extern int nd();

void may_swap2(int ***mmma, int ***mmmb) {
  if (nd()) {
    int **tmp = *mmma;
    *mmma = *mmmb;
    *mmmb = tmp;
  }
}
void may_swap(int **mma, int **mmb) {
  if (nd()) {
    int *tmp = *mma;
    *mma = *mmb;
    *mmb = tmp;
  }
}
void swap2_dec_three(int ***mmma, int ***mmmb, int ***mmmc) {
  may_swap2(mmma, mmmb);
  may_swap2(mmmb, mmmc);
  may_swap2(mmma, mmmb);
  may_swap(*mmma, *mmmb);
  may_swap(*mmmb, *mmmc);
  may_swap(*mmma, *mmmb);
  if (nd()) return;
  ***mmma -= 1;
  ***mmmb -= 2;
  ***mmmc -= 3;
  swap2_dec_three(mmma, mmmb, mmmc);
}
int main() {
  int a = nd(), b = nd(), c = nd();
  int a0 = a;
  int *ma = &a, *mb = &b, *mc = &c;
  int **mma = &ma, **mmb = &mb, **mmc = &mc;
  swap2_dec_three(&mma, &mmb, &mmc);
  sassert(a0 >= a && a0 - a <= 3);
  return 0;
}
