import java.util.Random;

public class UniqueScalarSafe {
  static class Int {
    int v;

    Int(int v_) {
      this.v = v_;
    }
  }

  public static void main(String[] args) {
    Random rand = new Random(0);
    Int x = new Int(0), y = new Int(0);
    Int p = rand.nextBoolean() ? x : y;
    p.v = 1;
    x.v += 1;
    assert x.v <= 2;
  }
}
