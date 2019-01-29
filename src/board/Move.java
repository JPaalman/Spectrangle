package group92.spectrangle.board;

import java.awt.*;

public class Move {

    public static void main(String[] args) {
        System.out.println(new Move(new Tile(6, Color.BLUE), 35));
    }

    private int index, rotation;
    private Tile tile;

    public Move(Tile tile, int index) {
        this(tile, index, 0);
    }

    public Move(Tile tile, int index, int rotation) {
        this.tile = tile;
        this.index = index;
        this.rotation = rotation;
    }

    public int getIndex() {
        return index;
    }

    public int getRotation() {
        return rotation;
    }

    public Tile getTile() {
        return tile;
    }

    public boolean equals(Object obj) {
        if (obj instanceof Move) {
            Move move = (Move) obj;
            return move.getIndex() == index && move.getTile().equals(tile);
        }
        return false;
    }

    public String toString() {
        tile.rotate(rotation);
        String result = tile.toString() + index + ";";
        tile.rotate(-rotation);
        return result;
    }


}
