package group92.spectrangle.protocol;

import group92.spectrangle.board.Piece;

public interface ClientProtocol extends Protocol {

    String scan();

    String connect(String username);

    String move(String username, Piece piece, int index);

    String swap(String username, Piece piece);

    String skip(String username);

    String quit(String username);

    String message(String message);

    String create(int players);

    String disconnect();

}
