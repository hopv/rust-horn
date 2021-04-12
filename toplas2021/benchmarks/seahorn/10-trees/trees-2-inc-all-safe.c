#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

void inc_all(Tree ta) {
  if (ta != NULL) {
    inc_all(ta->left);
    ta->val += 1;
    inc_all(ta->right);
  }
}
int sum(Tree ta) {
  if (ta == NULL) {
    return 0;
  } else {
    return sum(ta->left) + ta->val + sum(ta->right);
  }
}
int size(Tree ta) {
  if (ta == NULL) {
    return 0;
  } else {
    return size(ta->left) + 1 + size(ta->right);
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
  int n = sum(ta), s = size(ta);
  inc_all(ta);
  int r = sum(ta);
  sassert(r == n + s);
  return 0;
}
