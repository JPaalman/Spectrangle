package group92.spectrangle.board;

public class Move {

    public Move(Tile tile, int index) {
        this.tile = tile;
        this.index = index;
    }

    public int getIndex() {
        return index;
    }

    public Tile getTile() {
        return tile;
    }

    int index;
    Tile tile;
}
