#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

void append_some(Tree *pxs, Tree ys) {
  if (*pxs != NULL)
    nd() ? append_some(&((*pxs)->left), ys) : append_some(&((*pxs)->right), ys);
  else
    *pxs = ys;
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
  Tree xs = nd_tree(), ys = nd_tree();
  int m = sum(xs), n = sum(ys);
  append_some(&xs, ys);
  int r = sum(xs);
  sassert(r == m + n);
  return 0;
}
