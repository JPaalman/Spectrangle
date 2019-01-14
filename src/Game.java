package group92.spectrangle;

import java.util.Arrays;

public class Game {

    public static void main(String[] args) {
        if (Arrays.asList(args).contains("server")) {
            new Server();
        } else {
            new Client();
        }
    }

}
