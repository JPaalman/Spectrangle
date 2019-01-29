package group92.spectrangle.tests;

import group92.spectrangle.board.Tile;
import org.junit.jupiter.api.Test;

import static java.awt.Color.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

public class TileTest {

    @Test
    public void testEquals() {
        Tile tile1 = new Tile(1, RED, GREEN, BLUE);
        Tile tile2 = new Tile(1, BLUE, GREEN, RED);
        Tile tile3 = new Tile(1, RED);
        Tile tile4 = new Tile(2, BLUE, GREEN);
        assertEquals(tile1, tile1);
        assertEquals(tile1, tile2);
        assertNotEquals(tile3, tile1);
        assertNotEquals(tile1, tile4);
    }

}
