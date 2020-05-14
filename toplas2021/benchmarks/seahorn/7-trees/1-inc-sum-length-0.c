#include "seahorn/seahorn.h"
#include <stdlib.h>

extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

void inc(Tree xs) {
  if (xs != NULL) {
    inc(xs->left);
    xs->val += 1;
    inc(xs->right);
  }
}
int sum(Tree xs) {
  if (xs == NULL)
    return 0;
  else
    return sum(xs->left) + xs->val + sum(xs->right);
}
int size(Tree xs) {
  if (xs == NULL)
    return 0;
  else
    return size(xs->left) + 1 + size(xs->right);
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
  int n = sum(xs), s = size(xs);
  inc(xs);
  int r = sum(xs);
  sassert(r == n + s);
  return 0;
}
