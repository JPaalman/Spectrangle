package group92.spectrangle.board;

public class Move {

    private int index;

    private Piece piece;


    public Move(int index, Piece piece) {
        this.index = index;
        this.piece = piece;
    }

    public int getIndex() {
        return index;
    }

    public Piece getPiece() {
        return piece;
    }
}
