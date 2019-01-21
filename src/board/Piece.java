package group92.spectrangle.board;

import java.awt.*;

public class Piece {

    private int multiplier;
    private Color[] colors;

    public Piece(int multiplier, Color[] colors) {
        this.multiplier = multiplier;
        this.colors = colors;
    }

    public int getMultiplier() {
        return multiplier;
    }

    public Color getColor(int index) {
        return colors[index];
    }

}
