#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

struct Pair {
  int *mb;
  Tree tx2;
};
typedef struct Pair Pair;

Pair take_some_rest(Tree tx) {
  if (tx != NULL) {
    if (nd()) {
      Pair res = {&(tx->val), nd() ? tx->left : tx->right};
      return res;
    } else {
      return nd() ? take_some_rest(tx->left) : take_some_rest(tx->right);
    }
  } else {
    return take_some_rest(tx);
  }
}
int sum(Tree tx) {
  if (tx == NULL) {
    return 0;
  } else {
    return sum(tx->left) + tx->val + sum(tx->right);
  }
}
Tree nd_tree() {
  if (nd()) return NULL;
  Tree res = (Tree)malloc(sizeof(struct Node));
  res->left = nd_tree();
  res->right = nd_tree();
  return res;
}
int main() {
  Tree tx = nd_tree();
  int n = sum(tx);
  Pair pair = take_some_rest(tx);
  int *mb = pair.mb;
  Tree tx2 = pair.tx2;
  Pair pair2 = take_some_rest(tx2);
  int *mc = pair2.mb;
  *mb += 1;
  *mc += 1;
  int r = sum(tx);
  sassert(r > n + 2);
  return 0;
}
