package group92.spectrangle.tests;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.MoveException;
import org.junit.jupiter.api.Test;

import java.awt.*;

import static org.junit.jupiter.api.Assertions.*;

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

    @Test
    public void testFirstMove() {
        assertEquals(new Board().getPossibleFields(new Tile(6, Color.RED)).length, 36 - Board.MULTIPLICITY_4.size() - Board.MULTIPLICITY_3.size() - Board.MULTIPLICITY_2.size());
    }

    @Test
    public void testGetPossibleMoves() {
        Board board = new Board();
        try {
            board.place(new Tile(6, Color.RED), 0);
        } catch (MoveException e) {
            // should not occur
            fail();
        }
        assertTrue(board.getPossibleFields(new Tile(6, Color.RED)).length == 1);
    }

    @Test
    public void testPlace() {
        Board board = new Board();
        try {
            board.place(new Tile(6, Color.RED), 0);
        } catch (MoveException e) {
            // should not occur
            fail();
        }
        assertTrue(true);
    }

}
