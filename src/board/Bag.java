package group92.spectrangle.board;

import java.util.ArrayList;
import java.util.Arrays;

import static java.awt.Color.*;

public class Bag {

    public static final Tile[] TILES = {
            new Tile(6, YELLOW),
            new Tile(6, RED),
            new Tile(6, PINK),
            new Tile(6, GREEN),
            new Tile(6, BLUE),

            new Tile(5, YELLOW, RED),
            new Tile(5, YELLOW, PINK),
            new Tile(5, RED, GREEN),
            new Tile(5, RED, BLUE),
            new Tile(5, PINK, RED),
            new Tile(5, PINK, BLUE),
            new Tile(5, GREEN, YELLOW),
            new Tile(5, GREEN, PINK),
            new Tile(5, BLUE, YELLOW),
            new Tile(5, BLUE, GREEN),

            new Tile(4, YELLOW, GREEN),
            new Tile(4, YELLOW, BLUE),
            new Tile(4, RED, YELLOW),
            new Tile(4, RED, PINK),
            new Tile(4, PINK, YELLOW),
            new Tile(4, PINK, GREEN),
            new Tile(4, GREEN, RED),
            new Tile(4, GREEN, BLUE),
            new Tile(4, BLUE, RED),
            new Tile(4, BLUE, PINK),

            new Tile(3, YELLOW, BLUE, PINK),
            new Tile(3, RED, GREEN, YELLOW), new Tile(3, BLUE, GREEN, PINK),
            new Tile(3, GREEN, RED, BLUE),

            new Tile(2, YELLOW, PINK, RED),
            new Tile(2, YELLOW, PINK, GREEN),
            new Tile(2, BLUE, RED, PINK),

            new Tile(1, WHITE),
            new Tile(1, RED, YELLOW, BLUE),
            new Tile(1, GREEN, RED, PINK),
            new Tile(1, BLUE, YELLOW, GREEN)
    };

    private ArrayList<Tile> tiles;

    public Bag() {
        tiles = new ArrayList<>();
        tiles.addAll(Arrays.asList(TILES));
    }

    public ArrayList<Tile> getTiles() {
        return tiles;
    }

    public void put(Tile tile) {
        tiles.add(tile);
    }

    public Tile swap(Tile tile) {
        put(tile);
        return take();
    }

    public Tile take() {
        if(isEmpty()) {
            return null;
        }
        Tile out = tiles.get((int) (Math.random() * tiles.size()));
        tiles.remove(out);
        return out;
    }

    public boolean isEmpty() {
        return tiles.size() == 0;
    }

    public void removePiece(Tile tile) {
        tiles.remove(tile);
    }

    public void addPiece(Tile tile) {
        tiles.add(tile);
    }

}

