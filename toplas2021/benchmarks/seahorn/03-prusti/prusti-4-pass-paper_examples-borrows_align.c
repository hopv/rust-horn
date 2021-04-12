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
  Point **endBox = &segm._1;
  Point *endPt = &**endBox;
  int end_x = endPt->x;
  shift_x(endPt, segm._0->x - end_x);
  sassert(segm._0->x == segm._1->x);
  return 0;
}
