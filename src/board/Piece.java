package group92.spectrangle.board;

import group92.spectrangle.protocol.ClientProtocol;

import java.awt.*;

public class Piece {

    private int multiplier;
    private Color[] colors;

    public Piece(int multiplier, Color[] colors) {
        this.multiplier = multiplier;
        this.colors = colors;
    }

    public void flip() {
        Color[] result = new Color[3];
        for (int i = 0; i < 3; i++) {
            result[i] = colors[2 - i];
        }
        colors = result;
    }

    public void rotate(int rotation) {
        Color[] result = new Color[3];
        for (int i = 0; i < 3; i++) {
            result[i] = colors[(i + rotation) % 3];
        }
        colors = result;
    }

    public int getMultiplier() {
        return multiplier;
    }

    public Color getColor(int index) {
        return colors[index];
    }

    public Color[] getColors() {
        return colors.clone();
    }

    public String toString() {
        String result = multiplier + ";";
        for (Color color : colors) {
            result += ClientProtocol.COLORS.get(color);
        }
        return result;
    }


}
