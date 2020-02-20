public class IntTwoUnsafe {
  static class Int {
    int v;

    Int(int v_) {
      this.v = v_;
    }
  }

  public static void main(String[] args) {
    Int a = new Int(0);
    Int b = a;
    b.v += 1;
    assert a.v != 1;
  }
}
