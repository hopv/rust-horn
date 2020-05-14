#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

struct Pair {
  int *py;
  List xs2;
};
typedef struct Pair Pair;

Pair some(List xs) {
  if (xs != NULL)
    if (nd()) {
      Pair res = {&(xs->head), xs->tail};
      return res;
    } else
      return some(xs->tail);
  else
    return some(xs);
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
  List xs = nd_list();
  int n = sum(xs);
  Pair pair = some(xs);
  int *py = pair.py;
  List xs2 = pair.xs2;
  *py += 1;
  Pair pair2 = some(xs2);
  int *pz = pair2.py;
  *pz += 1;
  int r = sum(xs);
  sassert(r == n + 2);
  return 0;
}
