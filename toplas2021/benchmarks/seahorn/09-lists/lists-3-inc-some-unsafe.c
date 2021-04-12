#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

int *take_some(List la) {
  if (la != NULL) {
    return nd() ? &(la->head) : take_some(la->tail);
  } else {
    return take_some(la);
  }
}
int sum(List la) {
  if (la == NULL) {
    return 0;
  } else {
    return la->head + sum(la->tail);
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
  int n = sum(la);
  int *mb = take_some(la);
  *mb += 1;
  int r = sum(la);
  sassert(r > n + 1);
  return 0;
}
