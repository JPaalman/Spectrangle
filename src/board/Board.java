package group92.spectrangle.board;

import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.view.GUI;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Observable;

public class Board {

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

    public static int getIndexFromCoordinates(int row, int column) {
        if (row >= 0 && row <= 5 && column >= -row && column <= row) {
            return row ^ 2 + row + column;
        } else {
            return -1;
        }
    }

    public static int[] getCoordinatesFromIndex(int index) {
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

    // TODO find a better way of handling that exception
    public static List<Integer> getNeighbours(int row, int column) {
        ArrayList<Integer> neighbours = new ArrayList<>();
        // left
        neighbours.add(getIndexFromCoordinates(row, column - 1));
        // right
        neighbours.add(getIndexFromCoordinates(row, column + 1));
        if (rotation(row, column) == 0) {
            // bottom
            neighbours.add(getIndexFromCoordinates(row + 1, column));
        } else {
            // top
            neighbours.add(getIndexFromCoordinates(row - 1, column));
        }
        neighbours.remove(Integer.valueOf(-1));
        return neighbours;
    }

    public int place(Tile tile, int row, int column) throws MoveException {
        int index = getIndexFromCoordinates(row, column);
        int matchingSides = matchingSides(tile, index);
        if (matchingSides > 0) {
            return matchingSides * fields[index].place(tile);
        } else {
            throw new MoveException("no matching sides");
        }
    }

    // TODO implement
    private int matchingSides(Tile tile, int index) {
        return 1;
    }

    public int[] getPossibleMoves(Tile tile) {
        for (Field field : fields) {

        }
        return null;
    }

    private class Field extends Observable {

        private int multiplier;

        private Tile tile;

        public Field(int multiplier) {
            this.multiplier = multiplier;
            addObserver(GUI.get());
        }

        public int place(Tile tile) throws MoveException {
            if (this.tile == null) {
                this.tile = tile;
                setChanged();
                notifyObservers();
                return tile.getMultiplier() * multiplier;
            } else {
                throw new MoveException("field not empty");
            }
        }

        public boolean isEmpty() {
            return tile == null;
        }

    }

}
