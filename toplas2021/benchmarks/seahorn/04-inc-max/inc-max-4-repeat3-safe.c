#include "seahorn/seahorn.h"
extern int nd();

void inc_max_three(int *ma, int *mb, int *mc) {
  int *tmp;
  if (*ma < *mb) {
    int *tmp = ma;
    ma = mb;
    mb = tmp;
  }
  if (*mb < *mc) {
    int *tmp = mb;
    mb = mc;
    mc = tmp;
  }
  if (*ma < *mb) {
    int *tmp = ma;
    ma = mb;
    mb = tmp;
  }
  ma += 2;
  mb += 1;
}
void inc_max_three_repeat(int n, int *ma, int *mb, int *mc) {
  if (n != 0) {
    inc_max_three(ma, mb, mc);
    inc_max_three_repeat(n - 1, ma, mb, mc);
  }
}
int main() {
  int n = nd(), a = nd(), b = nd(), c = nd();
  inc_max_three_repeat(n, &a, &b, &c);
  sassert(a - b >= n || b - a >= n);
}
