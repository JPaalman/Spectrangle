package group92.spectrangle.protocol;

import group92.spectrangle.board.Piece;
import group92.spectrangle.players.Player;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;

public interface ClientProtocol {

    Map<Color, String> COLORS = new HashMap<Color, String>() {
        {
            put(Color.BLUE, "b");
            put(Color.GREEN, "g");
            put(Color.PINK, "p");
            put(Color.RED, "r");
            put(Color.WHITE, "w");
            put(Color.YELLOW, "y");
        }
    };

    String SCAN = "scan;";
    String CONNECT = "connect;";
    String JOIN = "join;";
    String CREATE = "create;";
    String START = "start;";
    String MOVE = "move;";
    String SWAP = "swap;";
    String SKIP = "skip;";
    String LEAVE = "leave;";
    String DISCONNECT = "disconnect;";
    String MESSAGE = "message;";

    String scan();

    String connect(Player player);

    String join();

    String join(String username);

    String join(int maxPlayers);

    String create();

    String create(int maxPlayers);

    String start();

    String move(Piece piece, int index);

    String swap(Piece piece);

    String skip();

    String leave();

    String disconnect();

    String message(String message);

}
