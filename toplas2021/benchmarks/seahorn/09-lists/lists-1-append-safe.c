#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

void append(List *mla, List lb) {
  if (*mla != NULL) {
    append(&((*mla)->tail), lb);
  } else {
    *mla = lb;
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
  List la = nd_list(), lb = nd_list();
  int m = sum(la), n = sum(lb);
  append(&la, lb);
  int r = sum(la);
  sassert(r == m + n);
  return 0;
}
