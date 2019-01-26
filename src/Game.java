package group92.spectrangle;

import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.players.HumanPlayer;
import group92.spectrangle.players.Player;

import java.util.ArrayList;

//the controller of our Spectrangle application

public class Game {

    private final String USAGE = "Usage: <server | client> + <name>";
    public final static int PORT = 2626;
//    private GUIServerBrowser gui;
    private ArrayList<Player> players;
    private int maxPlayers;

    public static void main(String[] args) {
        Game game = new Game();
//        game.start();
    }

    public Game() {
        maxPlayers = 4;
        players = new ArrayList<>();
    }

    public Game(int maxPlayers) {
        this.maxPlayers = maxPlayers;
        players = new ArrayList<>();
    }

    //return the max player count
    public int getMaxPlayers() {
        return maxPlayers;
    }

    //return the players list
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
        Player player = new HumanPlayer(name);
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
