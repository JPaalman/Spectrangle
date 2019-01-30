package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;

import java.util.ArrayList;
import java.util.Observable;

public abstract class Player extends Observable {

    private ArrayList<Tile> inventory;
    private String name;
    private int score;


    //Constructor for creating a new player object
    //@ requires name != null && !name.contains(";");
    //@ ensures score != null && inventory != null;
    //@ ensures getName() == name;
    public Player(String name) throws IllegalNameException {
        if(name != null && !name.contains(";")) {
            this.name = name;
        } else {
            throw new IllegalNameException("Illegal name");
        }
        score = 0;
        inventory = new ArrayList<Tile>();
    }

    public Player() {
        score = 0;
        inventory = new ArrayList<Tile>();
    }

    public void setName(String name) {
        this.name = name;
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

    //Increments the score of this player
    //@ requires score != null;
    //@ ensures getScore() == (old)getScore() + score;
    public int addScore(int score) {
        this.score += score;
        return score;
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

    public Tile swap(Tile in, Tile out) {
        if (inventory.contains(out)) {
            inventory.remove(out);
            inventory.add(in);
            return out;
        }
        return null;
    }

    // TODO implement
    // Makes a move for this player
    //@ requires board != null;
    public int makeMove(Board board) {
        return 0;
    }


    //Returns the inventory
    //@ pure
    public ArrayList<Tile> getInventory() {
        return inventory;
    }

    //Returns a String version of this player's inventory
    //@ pure
    public String inventoryToString() {
        String result = "";
        int i = 1;
        for (Tile tile : inventory) {
            result += "\n" +"Piece " + i + ": " + tile.toString();
            i++;
        }
        return result;
    }

    public void makeMove(Board board, Tile tile, int index) throws MoveException {
        addScore(board.place(tile, index));
        removePiece(tile);
    }

    //Returns a description of this player
    //@ pure
    public String toString() {
        return "name: " + getName() + "\nscore: " + getScore() + "\n" + "tiles: " + inventory.toString() + "\n";
    }

    //empties the inventory
    //@ requires inventory != null;
    public void emptyInventory() {
        inventory.clear();
    }



}
