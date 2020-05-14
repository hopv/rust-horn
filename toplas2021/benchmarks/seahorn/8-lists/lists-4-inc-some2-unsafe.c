#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Cons {
  int head;
  struct Cons *tail;
};
typedef struct Cons *List;

struct Pair {
  int *mb;
  List la2;
};
typedef struct Pair Pair;

Pair take_some_rest(List la) {
  if (la != NULL) {
    if (nd()) {
      Pair res = {&(la->head), la->tail};
      return res;
    } else {
      return take_some_rest(la->tail);
    }
  } else {
    return take_some_rest(la);
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
  Pair pair = take_some_rest(la);
  int *mb = pair.mb;
  List la2 = pair.la2;
  Pair pair2 = take_some_rest(la2);
  int *mc = pair2.mb;
  *mb += 1;
  *mc += 1;
  int r = sum(la);
  sassert(r > n + 2);
  return 0;
}
