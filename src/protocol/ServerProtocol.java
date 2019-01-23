package group92.spectrangle.protocol;

import group92.spectrangle.Game;
import group92.spectrangle.board.Piece;
import group92.spectrangle.players.Player;

public interface ServerProtocol extends Protocol {

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
