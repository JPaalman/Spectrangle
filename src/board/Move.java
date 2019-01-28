package group92.spectrangle.board;

public class Move {

    private int index;
    private Tile tile;

    public Move(int index, Tile tile) {
        this.index = index;
        this.tile = tile;
    }

    public int getIndex() {
        return index;
    }

    public Tile getTile() {
        return tile;
    }

}
