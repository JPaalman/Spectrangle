package group92.spectrangle.protocol;

import group92.spectrangle.Game;
import group92.spectrangle.board.Piece;
import group92.spectrangle.players.Player;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;

public interface ServerProtocol {

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

    String ANNOUNCE = "announce;";
    String RESPOND = "respond;";
    String GIVE = "give;";
    String TURN = "turn;";
    String MOVE = "move;";
    String SWAP = "swap;";
    String SKIP = "skip;";
    String END = "end;";
    String EXCEPTION = "exception;";
    String MESSAGE = "message;";

    String announce(String serverName);

    String respond(Game game, Game... games);

    String give(Player player, Piece piece, Piece... pieces);

    String turn(Player player);

    String move(Player player, Piece piece, int index);

    String swap(Player player, Piece piece);

    String skip(Player player);

    String end(Player player, Player... players);

    String exception(String message);

    String message(Player player, String message);

}
