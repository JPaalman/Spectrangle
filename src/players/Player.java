package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;

import java.util.ArrayList;
import java.util.Observable;

public abstract class Player extends Observable {

    private int counter;

    private ArrayList<Tile> inventory;
    private String name;
    private int score;


    //Constructor for creating a new player object
    //@ requires name != null && !name.contains(";");
    //@ ensures score != null && inventory != null;
    //@ ensures getName() == name;
    public Player(String name) throws IllegalNameException {
        if (name != null && !name.contains(";")) {
            this.name = name;
        } else {
            throw new IllegalNameException("Illegal name");
        }
        score = 0;
        inventory = new ArrayList<Tile>();
    }

    public Player() {
        counter = 0;
        score = 0;
        inventory = new ArrayList<Tile>();
    }

    //Adds a tile to this player's inventory
    //@ requires tile != null;
    //@ requires inventory.size() < 4;
    //@ ensures inventory.contains(tile);
    public boolean addPiece(Tile tile) {
        if (tile != null && inventory.size() < 4) {
            inventory.add(tile);
            return true;
        } else {
            return false;
        }
    }

    //Increments the score of this player
    //@ requires score != null;
    //@ ensures getScore() == (old)getScore() + score;
    public int addScore(int score) {
        this.score += score;
        return score;
    }

    //empties the inventory
    //@ requires inventory != null;
    public void emptyInventory() {
        inventory.clear();
    }

    //Returns the inventory
    //@ pure
    public ArrayList<Tile> getInventory() {
        return inventory;
    }

    //Returns the name of this player
    //@ requires name != null;
    //@ pure
    public String getName() {
        return name;
    }

    //Returns the score of this player
    //@ requires score != null;
    //@ pure
    public int getScore() {
        return score;
    }

    //Returns a String version of this player's inventory
    //@ pure
    public String inventoryToString() {
        String result = "";
        int i = 1;
        for (Tile tile : inventory) {
            result += "\n" + "Piece " + i + ": " + tile.toString();
            i++;
        }
        return result;
    }

    // TODO implement
    // Makes a move for this player
    //@ requires board != null;
    public int makeMove(Board board) {
        return 0;
    }

    // TODO throw after 3 exceptions
    public void makeMove(Board board, Tile tile, int index) throws MoveException {
        try {
            addScore(board.place(tile, index));
            removePiece(tile);
            counter = 0;
        } catch (MoveException e) {
            if (counter < 3) {
                tile.rotate(1);
                makeMove(board, tile, index);
                counter++;
            } else {
                counter = 0;
                throw e;
            }
        }
    }

    //Removes a tile from this player's inventory
    //@ requires tile != null;
    //@ requires inventory.contains(tile);
    //@ ensures !inventory.contains(tile);
    public boolean removePiece(Tile tile) {
        if (tile != null && inventory.contains(tile)) {
            inventory.remove(tile);
            return true;
        } else {
            return false;
        }
    }

    public void setName(String name) {
        this.name = name;
    }

    public Tile swap(Tile in, Tile out) {
        if (inventory.contains(out)) {
            inventory.remove(out);
            inventory.add(in);
            return out;
        }
        return null;
    }

    //Returns a description of this player
    //@ pure
    public String toString() {
        return "name: " + getName() + "\nscore: " + getScore() + "\n" + "tiles: " + inventory.toString() + "\n";
    }


}
