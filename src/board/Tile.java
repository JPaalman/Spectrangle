package group92.spectrangle.board;

import group92.spectrangle.protocol.Protocol;

import java.awt.*;
import java.util.Arrays;
import java.util.List;

public class Tile {

    private Color[] colors;
    private int multiplier;

    public Tile(int multiplier, Color... colors) {
        this.multiplier = multiplier;
        this.colors = new Color[3];
        for (int i = 0; i < this.colors.length; i++) {
            if (i < colors.length) {
                this.colors[i] = colors[i];
            } else {
                this.colors[i] = colors[colors.length - 1];
            }
        }
    }

    public Color[] getColors() {
        return colors.clone();
    }

    public int getMultiplier() {
        return multiplier;
    }

    public void rotate(int rotation) {
        Color[] result = new Color[3];
        for (int i = 0; i < 3; i++) {
            result[i] = colors[(i + rotation) % 3];
        }
        colors = result;
    }

    public boolean equals(Object obj) {
        if (obj instanceof Tile) {
            Tile tile = (Tile) obj;
            List<Color> tileColors = Arrays.asList(tile.colors);
            List<Color> myColors = Arrays.asList(colors);
            return myColors.containsAll(tileColors) && tileColors.containsAll(myColors);
        }
        return false;
    }

    public String toString() {
        String result = multiplier + ";";
        for (Color color : colors) {
            result += Protocol.COLOR_STRING_MAP.get(color) + ";";
        }
        return result;
    }

}
