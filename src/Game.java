package group92.spectrangle;

import group92.spectrangle.board.Bag;
import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.players.Player;

import java.util.ArrayList;
import java.util.Collections;

public class Game {

    private Bag bag;
    private Board board;
    private int maxPlayers;
    private ArrayList<Player> players;
    private boolean started = false;
    private int turnNumber;

    //initialize this game with a max players count
    //@ requires maxPlayers <= 4 && maxPlayers >= 2;
    //@ ensures maxPlayers != null && players != null && board != null && bag != null;
    public Game(int maxPlayers) {
        this.maxPlayers = maxPlayers;
        players = new ArrayList<>();
        board = new Board();
        bag = new Bag();
    }

    //adds a player to this game
    //@ requires player != null;
    //@ ensures players.contains(player);
    public void addPlayer(Player player) {
        players.add(player);
    }

    //removes a player from this game
    //@ requires player != null && players.contains(player);
    //@ ensures !players.contains(player);
    public void removePlayer(Player player) {
        players.remove(players.indexOf(player));
    }

    //distribute the first tiles, use this to determine who moves first based on the highest multiplier piece
    //if there is a draw then the bag resets and the players clear their inventory to redistribute pieces till there is a winner
    //@ requires players != null && bag != null;
    public void distributeFirstTiles() {
        Tile highestTile = null;
        boolean draw = false;
        for (Player p : players) {
            Tile newTile = bag.take();
            p.addPiece(newTile);
            if (highestTile == null || newTile.getMultiplier() > highestTile.getMultiplier()) {
                highestTile = newTile;
                draw = false;
                for (int i = players.indexOf(p); i > 0; i--) { //move the player to the first place
                    Collections.swap(players, i, i - 1);
                }
            } else if (newTile.getMultiplier() == highestTile.getMultiplier()) {
                draw = true;
                for (int i = players.indexOf(p); i > 0; i--) { //move the player to the first place
                    Collections.swap(players, i, i - 1);
                }
            }
        }

        if (draw) {
            bag = new Bag();
            for (Player p : players) {
                p.emptyInventory();
            }
            distributeFirstTiles();
            return;
        } else {
            int count = 1;
            while (count != 4) {//give all players 3 more pieces, totalling 4 pieces per player
                for (Player p : players) {
                    p.addPiece(bag.take());
                }
                count++;
            }
        }
    }

    //returns the bag
    //@ pure
    public Bag getBag() {
        return bag;
    }

    //returns the board
    //@ pure
    public Board getBoard() {
        return board;
    }

    //return the max player count
    //@ pure
    public int getMaxPlayers() {
        return maxPlayers;
    }

    //returns the name of the first player that is in this game
    //@ pure
    public String getName() {
        return players.get(0).getName();
    }

    //get a player with a specific name
    //@ requires name != null && players != null;
    public Player getPlayer(String name) {
        for (Player p : players) {
            if (p.getName() != null && p.getName().equals(name)) {
                return p;
            }
        }
        return null;
    }

    //return the players list
    //@ pure
    public ArrayList<Player> getPlayers() {
        return players;
    }

    //returns whether the game has started or not
    //@ pure
    public boolean getStarted() {
        return started;
    }

    //checks whether there is space for another player
    //@ pure
    public boolean hasSpace() {
        return players.size() < maxPlayers;
    }

    //increment the turn number
    //@ requires players != null && turnNumber != null;
    //@ ensures turnNumber == \old(turnNumber) + 1 % players.size;
    public void incrementTurn() {
        turnNumber = (turnNumber + 1) % players.size();
    }

    //starts the game
    //@ ensures turnNumber == 0 && started == true;
    public void start() {
        turnNumber = 0;
        distributeFirstTiles();
        started = true;
    }

    //return whose turn it is
    //@ requires players != null && turnNumber != null;
    //@ pure
    public Player turn() {//TODO separate method to increment
        return players.get(turnNumber);
    }
}
