package group92.spectrangle.protocol;

import group92.spectrangle.board.Tile;
import group92.spectrangle.players.Player;

public interface ClientProtocol extends Protocol {

    String scan();

    String connect(Player player);

    String join();

    String join(String username);

    String join(int maxPlayers);

    String create();

    String create(int maxPlayers);

    String start();

    String move(Tile tile, int index);

    String swap(Tile tile);

    String skip();

    String leave();

    String disconnect();

    String message(String message);

}
