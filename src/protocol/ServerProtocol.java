package group92.spectrangle.protocol;

import group92.spectrangle.Game;
import group92.spectrangle.board.Tile;
import group92.spectrangle.players.Player;

public interface ServerProtocol extends Protocol {

    String announce(String serverName);

    String respond(Game game, Game... games);

    String give(Player player, Tile tile, Tile... tiles);

    String turn(Player player);

    String move(Player player, Tile tile, int index);

    String swap(Player player, Tile tile, Tile returnedTile);

    String skip(Player player);

    String end(Player player, Player... players);

    String exception(String message);

    String message(Player player, String message);

}
