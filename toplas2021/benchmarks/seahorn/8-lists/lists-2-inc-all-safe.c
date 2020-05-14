#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

void inc(List la) {
  if (la != NULL) {
    la->head += 1;
    inc(la->tail);
  }
}
int sum(List la) {
  if (la == NULL) {
    return 0;
  } else {
    return la->head + sum(la->tail);
  }
}
int length(List la) {
  if (la == NULL) {
    return 0;
  } else {
    return 1 + length(la->tail);
  }
}
List nd_list() {
  if (nd()) return NULL;
  List res = (List)malloc(sizeof(struct Cons));
  res->tail = nd_list();
  return res;
}
int main() {
  List la = nd_list();
  int n = sum(la), l = length(la);
  inc(la);
  int r = sum(la);
  sassert(r == n + l);
  return 0;
}
