package group92.spectrangle.tests;

import group92.spectrangle.board.Piece;
import org.junit.jupiter.api.Test;

import static java.awt.Color.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

public class PieceTest {

    @Test
    public void testEquals() {
        Piece piece1 = new Piece(1, RED, GREEN, BLUE);
        Piece piece2 = new Piece(1, BLUE, GREEN, RED);
        Piece piece3 = new Piece(2, GREEN, GREEN, BLUE);
        assertEquals(piece1, piece1);
        assertEquals(piece1, piece2);
        assertNotEquals(piece1, piece3);
    }

}
