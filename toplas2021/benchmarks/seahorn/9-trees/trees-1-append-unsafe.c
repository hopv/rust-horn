#include "seahorn/seahorn.h"
#include <stdlib.h>
extern int nd();

struct Node {
  int val;
  struct Node *left, *right;
};
typedef struct Node *Tree;

void append(Tree *mla, Tree lb) {
  if (*mla != NULL) {
    nd() ? append(&((*mla)->left), lb) : append(&((*mla)->right), lb);
  } else {
    *mla = lb;
  }
}
int sum(Tree la) {
  if (la == NULL) {
    return 0;
  } else {
    return sum(la->left) + la->val + sum(la->right);
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
  Tree la = nd_tree(), lb = nd_tree();
  int m = sum(la), n = sum(lb);
  append(&la, lb);
  int r = sum(la);
  sassert(r > m + n);
  return 0;
}
