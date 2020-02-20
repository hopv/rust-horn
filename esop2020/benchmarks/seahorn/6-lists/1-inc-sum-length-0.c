#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

void inc(List xs) {
  if (xs != NULL) {
    xs->head += 1;
    inc(xs->tail);
  }
}
int sum(List xs) {
  if (xs == NULL)
    return 0;
  else
    return xs->head + sum(xs->tail);
}
int length(List xs) {
  if (xs == NULL)
    return 0;
  else
    return 1 + length(xs->tail);
}
List nd_list() {
  if (nd()) return NULL;
  List res = (List)malloc(sizeof(struct Cons));
  res->tail = nd_list();
  return res;
}

int main() {
  List xs = nd_list();
  int n = sum(xs), l = length(xs);
  inc(xs);
  int r = sum(xs);
  sassert(r == n + l);
  return 0;
}
