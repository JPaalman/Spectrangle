package group92.spectrangle.protocol;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;

public interface Protocol {

    String ANNOUNCE = "announce;";
    String CONNECT = "connect;";
    String EXCEPTION = "exception;";
    String GAMEOVER = "gameover;";
    String GIVE = "give;";
    String Message = "message;";
    String MOVE = "move;";
    String QUIT = "quit;";
    String SCAN = "scan;";
    String SKIP = "skip;";
    String SWAP = "swap;";
    String TURN = "turn";

    Map<Color, String> colors = new HashMap<Color, String>() {
        {
            put(Color.BLUE, "b");
            put(Color.GREEN, "g");
            put(Color.PINK, "p");
            put(Color.RED, "r");
            put(Color.WHITE, "w");
            put(Color.YELLOW, "y");
        }
    };

}
