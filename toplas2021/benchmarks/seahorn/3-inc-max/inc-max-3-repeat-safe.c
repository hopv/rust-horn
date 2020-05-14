#include "seahorn/seahorn.h"
extern int nd();

int *take_max(int *ma, int *mb) {
  if (*ma >= *mb) {
    return ma;
  } else {
    return mb;
  }
}
void inc_max_repeat(int n, int *ma, int *mb) {
  if (n > 0) {
    int *mc = take_max(ma, mb);
    *mc += 1;
    inc_max_repeat(n - 1, ma, mb);
  }
}
int main() {
  int n = nd(), a = nd(), b = nd();
  inc_max_repeat(n, &a, &b);
  sassert(a - b >= n || b - a >= n);
  return 0;
}
