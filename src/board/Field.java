package group92.spectrangle.board;

import group92.spectrangle.exceptions.MoveException;

public class Field {

    private int multiplier;

    private Tile tile;

    public Field(int multiplier) {
        this.multiplier = multiplier;
    }

    public Tile getTile() {
        return tile;
    }

    public int place(Tile tile) throws MoveException {
        if (this.tile == null) {
            this.tile = tile;
            return tile.getMultiplier() * multiplier;
        } else {
            throw new MoveException("field is not empty");
        }
    }

}