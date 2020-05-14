#include "seahorn/seahorn.h"
extern int nd();

int *take_max(int *ma, int *mb) {
  if (*ma >= *mb) {
    return ma;
  } else {
    return mb;
  }
}
int main() {
  int a = nd(), b = nd();
  int *mc = take_max(&a, &b);
  *mc += 1;
  sassert(a != b + 1);
  return 0;
}
