package group92.spectrangle;

import group92.spectrangle.board.Bag;
import group92.spectrangle.board.Board;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.players.ClientPlayer;
import group92.spectrangle.players.Player;

import java.util.ArrayList;

//the controller of our Spectrangle application

public class Game {

    private final String USAGE = "Usage: <server | client> + <name>";
    public final static int PORT = 2019;
    private ArrayList<Player> players;
    private int maxPlayers;
    private Board board;
    private Bag bag;

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
            if(p.getName().equals(name)) {
                return p;
            }
        }
        return null;
    }

    //starts the game
    public void start() {
        //TODO
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
        return players.get(0).getName();
    }

}
