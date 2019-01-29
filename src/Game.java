package group92.spectrangle;

import group92.spectrangle.board.Bag;
import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.players.ClientPlayer;
import group92.spectrangle.players.Player;

import java.util.ArrayList;
import java.util.Collections;

//the controller of our Spectrangle application

public class Game {

    private final String USAGE = "Usage: <server | client> + <name>";
    public final static int PORT = 2019;
    private ArrayList<Player> players;
    private int maxPlayers;
    private Board board;
    private Bag bag;
    private int turnNumber;
    private boolean started = false;


    public boolean getStarted() {
        return started;
    }

    public static void main(String[] args) {
        Game game = new Game(4);
//        game.start();
    }

    //initialize a game with a max players count
    //@ requires maxPlayers <= 4 && maxPlayers >= 2;
    //@ ensures maxPlayers != null && players != null && board != null && bag != null;
    public Game(int maxPlayers) {
        this.maxPlayers = maxPlayers;
        players = new ArrayList<>();
        board = new Board();
        bag = new Bag();
    }

    //@ pure
    public Board getBoard() {
        return board;
    }

    //@ pure
    public Bag getBag() {
        return bag;
    }

    //get a player with a specific name
    //@ requires name != null;
    public Player getPlayer(String name) {
        for(Player p : players) {
            if(p.getName() == null) {
                break;
            } else if(p.getName().equals(name)) {
                return p;
            }
        }
        return null;
    }

    //starts the game
    public void start() {
        turnNumber = 0;
        distributeFirstTiles();
        started = true;
    }

    //distribute the first tiles, use this to determine who moves first based on the highest multiplier piece
    //if there is a draw then the bag resets and the players clear their inventory to redistribute pieces till there is a winner
    public void distributeFirstTiles() {
        Tile highestTile = null;
        boolean draw = false;
        for(Player p : players) {
            Tile newTile = bag.take();
            p.addPiece(newTile);
            if(highestTile == null || newTile.getMultiplier() > highestTile.getMultiplier()) {
                highestTile = newTile;
                draw = false;
                for(int i = players.indexOf(p); i > 0; i--) { //move the player to the first place
                    Collections.swap(players, i, i - 1);
                }
            } else if(newTile.getMultiplier() == highestTile.getMultiplier()) {
                draw = true;
                for(int i = players.indexOf(p); i > 0; i--) { //move the player to the first place
                    Collections.swap(players, i, i - 1);
                }
            }
        }

        if(draw) {
            bag = new Bag();
            for(Player p : players) {
                p.emptyInventory();
            }
            distributeFirstTiles();
            return;
        } else {
            int count = 1;
            while(count != 4) {//give all players 3 more pieces, totalling 4 pieces per player
                for (Player p : players) {
                    p.addPiece(bag.take());
                }
                count++;
            }
        }
    }

    //return whose turn it is
    public Player turn() {//TODO separate method to increment
        return players.get(turnNumber);
    }

    //Increment the turn number
    public void incrementTurn() {
        turnNumber = (turnNumber + 1) % players.size() - 1;
    }

    //return the max player count
    //@ pure
    public int getMaxPlayers() {
        return maxPlayers;
    }

    //return the players list
    //@ pure
    public ArrayList<Player> getPlayers() {
        return players;
    }

    //checks whether there is space for another player
    public boolean hasSpace() {
        return players.size() < maxPlayers;
    }

//    public void start() {
//        GUIServerBrowser.launch(GUIServerBrowser.class);
//    }

    //adds a player to a game
    public void addPlayer(Player player) {
        players.add(player);
    }


    public void createClient(String name) throws IllegalNameException {
        Player player = new ClientPlayer(name);
        players.add(player);
    }

    public void errorMessage(String error) {
        System.out.println(error + "\n" + USAGE);
    }

    //returns the name of the first player that is in this game
    public String getName() {
        System.out.println(players);
        System.out.println(players.get(0));
        System.out.println(players.get(0).getName());
        return players.get(0).getName();
    }

}
