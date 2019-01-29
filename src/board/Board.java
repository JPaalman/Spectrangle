package group92.spectrangle.board;

import group92.spectrangle.Utils;
import group92.spectrangle.exceptions.MoveException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Board {

    public static final List<Integer> MULTIPLICITY_2 = Arrays.asList(10, 14, 30);
    public static final List<Integer> MULTIPLICITY_3 = Arrays.asList(2, 26, 35);
    public static final List<Integer> MULTIPLICITY_4 = Arrays.asList(11, 13, 20);

    public static int[] getCoordinatesFromIndex(int index) {
        if (isLegal(index)) {
            int row = (int) Math.sqrt(index);
            int column = index - (row ^ 2 + row);
            return new int[]{row, column};
        }
        return null;
    }

    public static int getIndexFromCoordinates(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getIndexFromCoordinates(row, column);
    }

    public static int getIndexFromCoordinates(int row, int column) {
        if (row >= 0 && row <= 5 && column >= -row && column <= row) {
            return row ^ 2 + row + column;
        }
        return -1;
    }

    public static boolean isLegal(int index) {
        return index >= 0 && index < 36;
    }

    public static boolean isLegal(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return isLegal(row, column);
    }

    public static boolean isLegal(int row, int column) {
        return row >= 0 && row <= 5 && column >= -row && column <= row;
    }

    private Field[] fields;

    public Board() {
        fields = new Field[36];
        for (int i = 0; i < fields.length; i++) {
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

    public int[] getPossibleFields(Tile tile) {
        ArrayList<Integer> possibleFields = new ArrayList<>();
        for (int i = 0; i < fields.length; i++) {
            if (fields[i].getTile() == null && getMatchingSides(tile, i) > 0) {
                possibleFields.add(i);
                }
        }
        return Utils.IntegerListToArray(possibleFields);
    }

    public int place(Tile tile, int index) throws MoveException {
        int matchingSides = getMatchingSides(tile, index);
        if (matchingSides > 0) {
            return matchingSides * fields[index].place(tile);
        } else {
            throw new MoveException("no matching sides");
        }
    }

    public boolean isValidMove(Tile tile, int index) {
        return getMatchingSides(tile, index) > 0 && fields[index].getTile() == null;
    }

    // returns an int with the amount of matching sides
    private int getMatchingSides(Tile tile, int index) {
        if (isLegal(index)) {
            int result = 0;
            int[] coordinates = getCoordinatesFromIndex(index);
            Field[] neighbouringFields = indicesToFields(getNeighbours(coordinates));
            for (int i = 0; i < neighbouringFields.length; i++) {
                if (neighbouringFields[i] != null && neighbouringFields[i].getTile() != null && tile.getColors()[i] == neighbouringFields[i].getTile().getColors()[2 - i]) {
                    result++;
                }
            }
            return result;
        }
        throw new IndexOutOfBoundsException();
    }

    private int[] getNeighbours(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getNeighbours(row, column);
    }

    // returns an int[] of the indices of the surrounding fields, from left to right
    // result array could contain null, if the field has less than 3 neighbours
    private int[] getNeighbours(int row, int column) {
        if (isLegal(row, column)) {
            int index;
            int[] neighbours = new int[3];

            // left neighbour
            index = getIndexFromCoordinates(row, column - 1);
            if (index >= 0) {
                neighbours[0] = index;
            }

            // top neighbour
            if (getRotation(row, column) == 1) {
                index = getIndexFromCoordinates(row - 1, column);
                if (index >= 0) {
                    neighbours[1] = index;
                }
            }

            // bottom neighbour
            if (getRotation(row, column) == 0) {
                index = getIndexFromCoordinates(row + 1, column);
                if (index >= 0) {
                    neighbours[1] = index;
                }
            }

            // right neighbour
            index = getIndexFromCoordinates(row, column + 1);
            if (index >= 0) {
                neighbours[2] = index;
            }

            return neighbours;
        }
        throw new IndexOutOfBoundsException();
    }

    // returns 0 for upwards, 1 for downwards
    private int getRotation(int row, int column) {
        if (isLegal(row, column)) {
            return (row + column) % 2;
        }
        throw new IndexOutOfBoundsException();
    }

    private int getRotation(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getRotation(row, column);
    }

    // returned Field[] might have empty fields on illegal indices
    private Field[] indicesToFields(int[] indices) {
        Field[] fields = new Field[indices.length];
        for (int i = 0; i < fields.length; i++) {
            if (isLegal(indices[i])) {
                fields[i] = this.fields[indices[i]];
            }
        }
        return fields;
    }

}
