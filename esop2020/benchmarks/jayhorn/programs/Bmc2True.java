import java.util.Random;

public class Bmc2True {
    public static void main(String[] args) {
        Random rand = new Random(0);
        int x = 1, y = 1;
        while (rand.nextBoolean()) {
            if (rand.nextBoolean()) {
                x++;
                y++;
            }
            if (rand.nextBoolean()) {
                x++;
            }
        }
        assert x >= y;
    }
}
