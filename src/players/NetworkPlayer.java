package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.network.Server;

public class NetworkPlayer extends Player {

    private Server.ConnectedClient connectedClient;

    //creates a network player with a connectedClient and a name, only used from the server side
    //@ requires name != null && !name.contains(";") && connectedClient != null;
    //@ ensures getName() == name && connectedClient != null;
    public NetworkPlayer(String name, Server.ConnectedClient connectedClient) throws IllegalNameException {
        super(name);
        this.connectedClient = connectedClient;
    }

    //creates a network player, only used from the client side
    public NetworkPlayer() {
    }

    //@ requires connectedClient != null;
    public Server.ConnectedClient getConnectedClient() {
        return connectedClient;
    }

    //make a move for this networkPlayer
    public void makeMove(Board board, Tile tile, int index) throws MoveException {
        int[] coords = Board.getCoordinatesFromIndex(index);
        super.addScore(board.place(tile, coords[0], coords[1]));
    }
}
