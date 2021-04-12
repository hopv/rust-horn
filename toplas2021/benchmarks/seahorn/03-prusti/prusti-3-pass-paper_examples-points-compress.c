#include "seahorn/seahorn.h"
#include <stdlib.h>

typedef struct Point {
  int x, y;
} Point;
typedef struct Pair {
  Point *_0, *_1;
} Pair;

extern Point nd();

void shift_x(Point *p, int s) { p->x = p->x + s; }

int main() {
  Pair segm = {(Point *)malloc(sizeof(Point)), (Point *)malloc(sizeof(Point))};
  *segm._0 = nd();
  *segm._1 = nd();
  int diff = segm._0->x - segm._1->x + 1;
  shift_x(&segm._1, diff);
  sassert(segm._0->x < segm._1->x);
  return 0;
}
