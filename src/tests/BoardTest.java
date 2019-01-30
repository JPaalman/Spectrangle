package group92.spectrangle.tests;

import group92.spectrangle.board.Board;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class BoardTest {

    @Test
    public void testConvert() {
        int index = 11;
        int result = Board.getIndexFromCoordinates(Board.getCoordinatesFromIndex(index));
        assertEquals(index, result);
    }

    @Test
    public void testConvertBackwards() {
        int[] coordinates = {3, 0};
        int[] result = Board.getCoordinatesFromIndex(Board.getIndexFromCoordinates(coordinates));
        for (int i = 0; i < 2; i++) {
            assertEquals(coordinates[i], result[i]);
        }
    }

}
