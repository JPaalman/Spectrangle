package group92.spectrangle.protocol;

import group92.spectrangle.board.Piece;

public interface ServerProtocol extends Protocol {

    String announce(String gamename);

    String give(String username, Piece... piece);

    String turn(String username);

    String move(String username, Piece piece, int index, int rotation);

    String move(String username, Piece piece, int index);

    String skip(String username);

    String swap(String username, Piece receivedPiece, Piece returnedPiece);

    String exception(String message);

    String gameover(String... winner);

}
