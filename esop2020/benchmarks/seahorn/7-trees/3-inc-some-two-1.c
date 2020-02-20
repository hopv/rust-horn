#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

struct Pair {
  int *py;
  Tree xs2;
};
typedef struct Pair Pair;

Pair some(Tree xs) {
  if (xs != NULL)
    if (nd()) {
      Pair res = {&(xs->val), nd() ? &(xs->left) : &(xs->right)};
      return res;
    } else
      return nd() ? some(xs->left) : some(xs->right);
  else
    return some(xs);
}
int sum(Tree xs) {
  if (xs == NULL)
    return 0;
  else
    return sum(xs->left) + xs->val + sum(xs->right);
}
Tree nd_tree() {
  if (nd()) return NULL;
  Tree res = (Tree)malloc(sizeof(struct Node));
  res->left = nd_tree();
  res->right = nd_tree();
  return res;
}

int main() {
  Tree xs = nd_tree();
  int n = sum(xs);
  Pair pair = some(xs);
  int *py = pair.py;
  Tree xs2 = pair.xs2;
  *py += 1;
  Pair pair2 = some(xs2);
  int *pz = pair2.py;
  *pz += 1;
  int r = sum(xs);
  sassert(r > n + 2);
  return 0;
}
