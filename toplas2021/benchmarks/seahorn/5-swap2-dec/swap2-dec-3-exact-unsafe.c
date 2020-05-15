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
void swap2_dec_bound(int n, int ***mmma, int ***mmmb) {
  may_swap2(mmma, mmmb);
  may_swap(*mmma, *mmmb);
  if (n == 0) return;
  ***mmma -= 1;
  ***mmmb -= 2;
  swap2_dec_bound(n - 1, mmma, mmmb);
}
int main() {
  int n = nd(), a = nd(), b = nd();
  int a0 = a;
  int *ma = &a, *mb = &b;
  int **mma = &ma, **mmb = &mb;
  swap2_dec_bound(n, &mma, &mmb);
  sassert(a0 >= a && a0 - a < 2 * n);
  return 0;
}
