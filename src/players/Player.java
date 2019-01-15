package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Piece;

import java.util.ArrayList;

public abstract class Player {

    private ArrayList<Piece> inventory;
    private String name;
    private int score;


    //Constructor for creating a new player object
    //@ requires name != null;
    //@ ensures score != null;
    //@ ensures getName() == name;
    public Player(String name) {
        this.name = name;
        score = 0;
        inventory = new ArrayList<Piece>();
    }

    //Returns the name of this player
    //@ pure
    public String getName() {
        return name;
    }

    //Returns the score of this player
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

    //Adds a piece to this player's inventory
    //@ requires piece != null;
    //@ requires inventory.size() < 4;
    //@ ensures inventory.contains(piece);
    public boolean addPiece(Piece piece) {
        if(piece != null && inventory.size() < 4) {
            inventory.add(piece);
            return true;
        } else {
            return false;
        }
    }

    //Removes a piece from this player's inventory
    //@ requires piece != null;
    //@ requires inventory.contains(piece);
    //@ ensures !inventory.contains(piece);
    public boolean removePiece(Piece piece) {
        if(piece != null && inventory.contains(piece)) {
            inventory.remove(piece);
            return true;
        } else {
            return false;
        }
    }

    //Makes a move for this player
    //@ requires board != null;
    public abstract int makeMove(Board board);

    //Returns the inventory
    //@ pure
    public ArrayList<Piece> getInventory() {
        return inventory;
    }

    //Returns a String version of this player's inventory
    //@ pure
    public String inventoryToString() {
        String result = "";
        for(Piece piece : inventory) {
            result += "\n" + piece.toString();
        }
        return result;
    }

    //Returns a description of this player
    //@ pure
    public String toString() {
        return "Name: " + getName() + " score: " + getScore() + "\n" + "Pieces: " + inventoryToString();
    }



}
