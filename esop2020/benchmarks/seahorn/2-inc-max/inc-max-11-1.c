#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

void inc_max_three(int *px, int *py, int *pz) {
  int *tmp;
  if (*px > *py) {
    int *tmp = px;
    px = py;
    py = tmp;
  }
  if (*py > *pz) {
    int *tmp = py;
    py = pz;
    pz = tmp;
  }
  if (*px > *py) {
    int *tmp = px;
    px = py;
    py = tmp;
  }
  py += 1;
  pz += 2;
}
void inc_max_three_repeat(int n, int *px, int *py, int *pz) {
  if (n > 0) {
    inc_max_three(px, py, pz);
    inc_max_three_repeat(n - 1, px, py, pz);
  }
}
int main() {
  int n = nd(), x = nd(), y = nd(), z = nd();
  inc_max_three_repeat(n, &x, &y, &z);
  sassert(x - y > n || y - x > n);
}
