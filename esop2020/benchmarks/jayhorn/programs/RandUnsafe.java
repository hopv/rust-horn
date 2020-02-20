import java.util.Random;

public class RandUnsafe {
  public static void main(String[] args) {
    Random rand = new Random(0);
    int a = rand.nextInt();
    assert false;
  }
}
