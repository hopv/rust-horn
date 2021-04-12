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
void swap2_dec(int ***mmma, int ***mmmb) {
  may_swap2(mmma, mmmb);
  may_swap(*mmma, *mmmb);
  if (nd()) return;
  ***mmma -= 1;
  ***mmmb -= 2;
  swap2_dec(mmma, mmmb);
}
int main() {
  int a = nd(), b = nd();
  int a0 = a;
  int *ma = &a, *mb = &b;
  int **mma = &ma, **mmb = &mb;
  swap2_dec(&mma, &mmb);
  sassert(a0 >= a && a0 - a <= 3);
  return 0;
}
