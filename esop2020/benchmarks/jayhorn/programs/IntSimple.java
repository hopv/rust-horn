public class IntSimple {
  static class Int {
    int v;

    Int(int v_) {
      this.v = v_;
    }
  }

  public static void main(String[] args) {
    Int a = new Int(0);
    assert a.v == 1;
  }
}
