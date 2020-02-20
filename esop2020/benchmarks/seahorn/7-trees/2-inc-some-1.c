#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

int *some(Tree xs) {
  if (xs != NULL)
    return nd() ? &(xs->val) : nd() ? some(xs->left) : some(xs->right);
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
  int *py = some(xs);
  *py += 1;
  int r = sum(xs);
  sassert(r > n + 1);
  return 0;
}
