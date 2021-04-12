#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

int *inc_some(Tree ta) {
  if (ta != NULL) {
    return nd() ? &(ta->val) : nd() ? inc_some(ta->left) : inc_some(ta->right);
  } else {
    return inc_some(ta);
  }
}
int sum(Tree ta) {
  if (ta == NULL) {
    return 0;
  } else {
    return sum(ta->left) + ta->val + sum(ta->right);
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
  Tree ta = nd_tree();
  int n = sum(ta);
  int *mb = inc_some(ta);
  *mb += 1;
  int r = sum(ta);
  sassert(r == n + 1);
  return 0;
}
