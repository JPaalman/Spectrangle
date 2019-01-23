package group92.spectrangle.protocol;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;

public interface Protocol {

    Map<Color, String> COLOR_STRING_MAP = new HashMap<Color, String>() {
        {
            put(Color.BLUE, "b");
            put(Color.GREEN, "g");
            put(Color.PINK, "p");
            put(Color.RED, "r");
            put(Color.WHITE, "w");
            put(Color.YELLOW, "y");
        }
    };

    Map<String, Color> STRING_COLOR_MAP = new HashMap<String, Color>() {
        {
            put("b", Color.BLUE);
            put("g", Color.GREEN);
            put("p", Color.PINK);
            put("r", Color.RED);
            put("w", Color.WHITE);
            put("y", Color.YELLOW);
        }
    };

    String ANNOUNCE = "announce";
    String CONNECT = "connect";
    String CREATE = "create";
    String DISCONNECT = "disconnect";
    String END = "end";
    String EXCEPTION = "exception";
    String GIVE = "give";
    String JOIN = "join";
    String LEAVE = "leave";
    String MESSAGE = "message";
    String MOVE = "move";
    String RESPOND = "respond";
    String SCAN = "scan";
    String SKIP = "skip";
    String START = "start";
    String SWAP = "swap";
    String TURN = "turn";

}
