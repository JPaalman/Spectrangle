package group92.spectrangle.board;

import java.util.ArrayList;
import java.util.Arrays;

import static java.awt.Color.*;

public class Bag {

    public static final Piece[] PIECES = new Piece[]{new Piece(6, YELLOW), new Piece(6, RED), new Piece(6, PINK), new Piece(6, GREEN), new Piece(6, BLUE),

            new Piece(5, YELLOW, RED), new Piece(5, YELLOW, PINK), new Piece(5, RED, GREEN), new Piece(5, RED, BLUE), new Piece(5, PINK, RED), new Piece(5, PINK, BLUE), new Piece(5, GREEN, YELLOW), new Piece(5, GREEN, PINK), new Piece(5, BLUE, YELLOW), new Piece(5, BLUE, GREEN),

            new Piece(4, YELLOW, GREEN), new Piece(4, YELLOW, BLUE), new Piece(4, RED, YELLOW), new Piece(4, RED, PINK), new Piece(4, PINK, YELLOW), new Piece(4, PINK, GREEN), new Piece(4, GREEN, RED), new Piece(4, GREEN, BLUE), new Piece(4, BLUE, RED), new Piece(4, BLUE, PINK),

            new Piece(3, YELLOW, BLUE, PINK), new Piece(3, RED, GREEN, YELLOW), new Piece(3, GREEN, RED, BLUE),

            new Piece(2, YELLOW, PINK, RED), new Piece(2, YELLOW, PINK, GREEN), new Piece(2, BLUE, RED, PINK),

            new Piece(1, WHITE), new Piece(1, RED, YELLOW, BLUE), new Piece(1, GREEN, RED, PINK), new Piece(1, BLUE, YELLOW, GREEN)};

    private ArrayList<Piece> pieces;

    public Bag() {
        pieces = new ArrayList<>();
        pieces.addAll(Arrays.asList(PIECES));
    }

    public Piece take() {
        Piece out = pieces.get((int) (Math.random() * pieces.size()));
        pieces.remove(out);
        return out;
    }

    public void put(Piece piece) {
        pieces.add(piece);
    }

}

