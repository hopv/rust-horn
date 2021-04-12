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
int main() {
  int a = nd(), b = nd(), c = nd();
  inc_max_three(&a, &b, &c);
  sassert(a != b);
}
