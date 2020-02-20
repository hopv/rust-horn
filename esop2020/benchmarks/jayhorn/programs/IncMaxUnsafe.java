import java.util.Random;

public class IncMaxUnsafe {
  static class Int {
    int v;

    Int(int v_) {
      this.v = v_;
    }
  }

  public static void main(String[] args) {
    Random rand = new Random(0);
    Int a = new Int(rand.nextInt()), b = new Int(rand.nextInt());
    Int c = a.v >= b.v ? a : b;
    c.v += 1;
    assert a.v != b.v + 1;
  }
}
