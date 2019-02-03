package group92.spectrangle.board;

import group92.spectrangle.Utils;
import group92.spectrangle.exceptions.MoveException;

import java.awt.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Board {

    // TODO check for field with multiplicity > 1 on first move

    public static final List<Integer> MULTIPLICITY_2 = Arrays.asList(10, 14, 30);
    public static final List<Integer> MULTIPLICITY_3 = Arrays.asList(2, 26, 35);
    public static final List<Integer> MULTIPLICITY_4 = Arrays.asList(11, 13, 20);

    //@ pure
    //@ requires isLegal(index) == true;
    //@ ensures \result.length == 2;

    /**
     * convert an index to it's coordinates
     *
     * @param index
     * @return an int[] containing the row and column
     */
    public static int[] getCoordinatesFromIndex(int index) {
        assert isLegal(index);
        if (isLegal(index)) {
            int row = (int) Math.sqrt(index);
            int column = index - (int) Math.pow(row, 2) - row;
            return new int[]{row, column};
        }
        throw new RuntimeException("index considered illegal");
    }

    //@ pure

    /**
     * convert a set coordinates to it's index
     * @param coordinates an int[] containing a row and column
     * @return the corresponding index
     */
    public static int getIndexFromCoordinates(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getIndexFromCoordinates(row, column);
    }

    /**
     * convert a set coordinates to it's index
     * @param row
     * @param column
     * @return the corresponding index
     */
    //@ pure
    //@ ensures isLegal(row, column) ? isLegal(\result) : \result == -1;
    public static int getIndexFromCoordinates(int row, int column) {
        if (isLegal(row, column)) {
            return (int) Math.pow(row, 2) + row + column;
        }
        return -1;
    }

    /**
     * check if an index is legal (exists on the board)
     * @param index
     * @return true or false
     */
    //@ pure
    //@ ensures \result == index >= 0 && index < 36;
    public static boolean isLegal(int index) {
        return index >= 0 && index < 36;
    }

    /**
     * check if an index is legal (exists on the board)
     * @param coordinates an int[] containing a row and column
     * @return true or false
     */
    //@ pure
    public static boolean isLegal(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return isLegal(row, column);
    }

    /**
     * check if an index is legal (exists on the board)
     * @param row
     * @param column
     * @return true or false
     */
    //@ pure
    //@ ensures \result == row >= 0 && row <= 5 && column >= -row && column <= row;
    public static boolean isLegal(int row, int column) {
        return row >= 0 && row <= 5 && column >= -row && column <= row;
    }

    //@ private invariant fields != null;
    private Field[] fields;

    private boolean first;

    /**
     * make a new board, with 36 empty fields
     */
    //@ ensures first;
    public Board() {
        first = true;
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

    /**
     * get all indices where the given piece can be placed
     * @param tile
     * @return an int[] of indices where the given tile can be placed
     */
    //@ pure
    //@ ensures \result != null;
    //@ requires tile != null;
    public int[] getPossibleFields(Tile tile) {
        assert tile != null;
        ArrayList<Integer> possibleFields = new ArrayList<>();
        for (int i = 0; i < fields.length; i++) {
            if (isValidMove(tile, i)) {
                possibleFields.add(i);
            }
        }
        return Utils.IntegerListToArray(possibleFields);
    }

    /**
     * check if a move is legal
     * @param tile
     * @param index
     * @return true or false
     */
    //@ pure
    //@ ensures \result == first && !MULTIPLICITY_4.contains(index) && !MULTIPLICITY_3.contains(index) &&
    // !MULTIPLICITY_2.contains(index)) || (getMatchingSides(tile, index) > 0 && fields[index].getTile() == null);
    public boolean isValidMove(Tile tile, int index) {
        return (first && !MULTIPLICITY_4.contains(index) && !MULTIPLICITY_3.contains(index) && !MULTIPLICITY_2.contains(index)) || (getMatchingSides(tile, index) > 0 && fields[index].getTile() == null);
    }

    /**
     * place a tile on board
     * @param tile
     * @param index
     * @return the score of the move
     * @throws MoveException if an illegal move is made
     */
    //@ requires isValidMove(tile, index);
    //@ ensures \result > 0
    public int place(Tile tile, int index) throws MoveException {
        assert isValidMove(tile, index);
        if (first) {
            if (!MULTIPLICITY_4.contains(index) && !MULTIPLICITY_3.contains(index) && !MULTIPLICITY_2.contains(index)) {
                fields[index].place(tile);
                first = false;
                return tile.getMultiplier();
            } else {
                throw new MoveException("first move cannot be placed on a field with a multiplier");
            }
        }
        int matchingSides = getMatchingSides(tile, index);
        if (matchingSides > 0) {
            return matchingSides * fields[index].place(tile);
        } else {
            throw new MoveException("no matching sides");
        }
    }

    /**
     * get the future amount of matching sides with the neighbouring fields, returns 0 if not all sides match
     * @param tile
     * @param index
     * @return the amount of matching sides with the neighbouring pieces
     */
    // returns an int with the amount of matching sides
    //@ pure
    //@ requires isLegal(index);
    //@ ensures \result == 0 || \result == counter && \result <= 3;
    private int getMatchingSides(Tile tile, int index) {
        assert isLegal(index);
        if (isLegal(index)) {
            int counter = 0, result = 0;
            int[] coordinates = getCoordinatesFromIndex(index);
            Field[] neighbouringFields = indicesToFields(getNeighbours(coordinates));

            for (int i = 0; i < neighbouringFields.length; i++) {
                if (neighbouringFields[i] != null && neighbouringFields[i].getTile() != null) {
                    counter++;
                    if ((tile.getColors()[i].equals(Color.WHITE) || tile.getColors()[i] == neighbouringFields[i].getTile().getColors()[2 - i])) {
                        result++;
                    }
                }
            }

            if (result == counter) {
                return result;
            }
            return 0;
        }
        throw new IndexOutOfBoundsException();
    }

    /**
     * Get the indices of the neighbouring fields
     * @param coordinates an int[] containing a row and column
     * @return an int[] of indices of neighbouring fields, contains -1 for neighbours that don't exist
     */
    //@ pure
    private int[] getNeighbours(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getNeighbours(row, column);
    }

    /**
     * Get the indices of the neighbouring fields
     * @param row
     * @param column
     * @return an int[] of indices of neighbouring fields, contains -1 for neighbours that don't exist
     */
    // returns an int[] of the indices of the surrounding fields, from left to right
    // resulting array could contain -1, if the field has less than 3 neighbours
    //@ requires isLegal(row, column);
    //@ ensures \result.length == 3;
    private int[] getNeighbours(int row, int column) {
        assert isLegal(row, column);
        if (isLegal(row, column)) {
            int index;
            int[] neighbours = new int[3];

            // left neighbour
            neighbours[0] = getIndexFromCoordinates(row, column - 1);

            // top neighbour
            if (getRotation(row, column) == 1) {
                neighbours[1] = getIndexFromCoordinates(row - 1, column);
            }

            // bottom neighbour
            if (getRotation(row, column) == 0) {
                neighbours[1] = getIndexFromCoordinates(row + 1, column);
            }

            // right neighbour
            neighbours[2] = getIndexFromCoordinates(row, column + 1);

            return neighbours;
        }
        throw new IndexOutOfBoundsException();
    }

    /**
     * get the rotation of a field on the board
     * @param row
     * @param column
     * @return 0 for upwards, 1 for downwards
     */
    //@ pure
    //@ requires isLegal(row, column);
    //@ ensures \result == (row + column) % 2;
    private int getRotation(int row, int column) {
        assert isLegal(row, column);
        if (isLegal(row, column)) {
            return (row + column) % 2;
        }
        throw new IndexOutOfBoundsException();
    }

    /**
     * get the rotation of a field on the board
     * @param coordinates an int[] containing a row and column
     * @return 0 for upwards, 1 for downwards
     */
    //@ pure
    private int getRotation(int[] coordinates) {
        int row = coordinates[0];
        int column = coordinates[1];
        return getRotation(row, column);
    }

    /**
     * convert an int[] of indices to a Field[] of matching fields
     * @param indices an int[] of indices
     * @return a Field[] with the corresponding fields
     */
    // returned Field[] might have empty fields on illegal indices
    //@ pure
    //@ requires indices != null;
    //@ ensures indices.length == \result.length;
    private Field[] indicesToFields(int[] indices) {
        assert indices != null;
        Field[] fields = new Field[indices.length];
        for (int i = 0; i < fields.length; i++) {
            if (isLegal(indices[i])) {
                fields[i] = this.fields[indices[i]];
            }
        }
        return fields;
    }

}
