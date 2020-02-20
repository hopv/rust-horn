import java.util.Random;

public class Bmc1False {
    public static void main(String[] args) {
        Random rand = new Random(0);
        int x = 1, y = 1;
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        if (rand.nextBoolean()) {
            x++;
            y++;
        }
        assert x <= 10;
    }
}
