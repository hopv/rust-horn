#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

int *some(List xs) {
  if (xs != NULL)
    return nd() ? &(xs->head) : some(xs->tail);
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
  int *py = some(xs);
  *py += 1;
  int r = sum(xs);
  sassert(r > n + 1);
  return 0;
}
