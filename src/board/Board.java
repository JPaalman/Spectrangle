package group92.spectrangle.board;

import group92.spectrangle.exceptions.MoveException;

import java.util.Arrays;
import java.util.List;

public class Board {

    // TODO program methods for getting neighbouring fields

    public static final List<Integer> MULTIPLICITY_4 = Arrays.asList(11, 13, 20);
    public static final List<Integer> MULTIPLICITY_3 = Arrays.asList(2, 26, 35);
    public static final List<Integer> MULTIPLICITY_2 = Arrays.asList(10, 14, 30);
    private Field[] fields;

    public Board() {
        fields = new Field[36];
        for (int i = 0; i < 36; i++) {
            if (MULTIPLICITY_4.contains(i)) {
                fields[i] = new Field(4);
            } else if (MULTIPLICITY_3.contains(i)) {
                fields[i] = new Field(3);
            } else if (MULTIPLICITY_2.contains(i)) {
                fields[i] = new Field(2);
            } else {
                fields[i] = new Field(1);
            }
        }
    }

    public static int getIndexFromCoordinates(int row, int column) throws IndexOutOfBoundsException {
        if (row >= 0 && row <= 5 && column >= -row && column <= row) {
            return row ^ 2 + row + column;
        } else {
            throw new IndexOutOfBoundsException();
        }
    }

    public static int[] getCoordinatesFromIndex(int index) throws IndexOutOfBoundsException {
        if (index >= 0 && index < 36) {
            int row = (int) Math.sqrt(index);
            int column = index - (row ^ 2 + row);
            return new int[]{row, column};
        } else {
            throw new IndexOutOfBoundsException();
        }
    }

    // returns 0 for upwards, 1 for downwards
    public static int rotation(int row, int column) {
        return (row + column) % 2;
    }

    public int place(Piece piece, int row, int column) throws MoveException {
        int index = getIndexFromCoordinates(row, column);
        int matchingSides = matchingSides(piece, index);
        if (matchingSides > 0) {
            return matchingSides * fields[index].place(piece);
        } else {
            throw new MoveException("no matching sides");
        }
    }

    // TODO implement
    private int matchingSides(Piece piece, int index) {
        return 1;
    }

    private class Field {

        private int multiplier;

        private Piece piece;

        public Field(int multiplier) {
            this.multiplier = multiplier;
        }

        public int place(Piece piece) throws MoveException {
            if (this.piece == null) {
                this.piece = piece;
                return piece.getMultiplier() * multiplier;
            } else {
                throw new MoveException("field not empty");
            }
        }

    }

}
