#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

void append(List *pxs, List ys) {
  if (*pxs != NULL)
    append(&((*pxs)->tail), ys);
  else
    *pxs = ys;
}
int sum(List xs) {
  if (xs == NULL)
    return 0;
  else
    return xs->head + sum(xs->tail);
}
List nd_list() {
  if (nd()) return NULL;
  List res = (List)malloc(sizeof(struct Cons));
  res->tail = nd_list();
  return res;
}

int main() {
  List xs = nd_list(), ys = nd_list();
  int m = sum(xs), n = sum(ys);
  append(&xs, ys);
  int r = sum(xs);
  sassert(r == m + n);
  return 0;
}
