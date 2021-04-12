#include "seahorn/seahorn.h"
extern int nd();

int ack(int m, int n) {
  if (m == 0) {
    return n + 1;
  } else if (n == 0) {
    return ack(m - 1, 1);
  } else {
    return ack(m - 1, ack(m, n - 1));
  }
}
int main() {
  int m = nd(), n = nd();
  if (0 <= m && 0 <= n) {
    sassert(ack(m, n) >= 0);
  }
  return 0;
}
