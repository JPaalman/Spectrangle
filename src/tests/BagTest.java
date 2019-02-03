package group92.spectrangle.tests;

import group92.spectrangle.board.Bag;
import group92.spectrangle.board.Tile;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BagTest {

    @Test
    public void testSwap() {
        Bag bag = new Bag();
        Tile tile = bag.take();
        bag.swap(tile);
        boolean result = false;
        while (!bag.isEmpty()) {
            if (bag.take() == tile) {
                result = true;
                break;
            }
        }
        assertTrue(result);
    }

    @Test
    public void testTake() {
        Bag bag = new Bag();
        System.out.println(Bag.TILES.length);
        for (int i = 0; i < 36; i++) {
            assertNotEquals(bag.take(), null);
        }
        assertTrue(bag.isEmpty());
    }


}
