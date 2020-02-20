#include "seahorn/seahorn.h"
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
int main() {
  int x = nd(), y = nd(), z = nd();
  inc_max_three(&x, &y, &z);
  sassert(x != y);
}
