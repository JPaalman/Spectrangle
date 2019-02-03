package group92.spectrangle;

import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Client;
import group92.spectrangle.network.Server;

public class Main {

    public static void main(String[] args) {
        if (args.length > 0) {
            try {
                new Server(args[0]);
            } catch (IllegalNameException e) {
                throw new RuntimeException("illegal server name");
            }
        } else {
            new Client();
        }
    }

}
