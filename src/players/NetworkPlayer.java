package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Server;

public class NetworkPlayer extends Player {

    private Server.ConnectedClient connectedClient;

    //creates a network player with a connectedClient and a name
    //@ requires name != null && !name.contains(";") && connectedClient != null;
    //@ ensures getName() == name && connectedClient != null;
    public NetworkPlayer(String name, Server.ConnectedClient connectedClient) throws IllegalNameException {
        super(name);
        this.connectedClient = connectedClient;
    }

    //@ requires connectedClient != null;
    public Server.ConnectedClient getConnectedClient() {
        return connectedClient;
    }

    @Override
    public int makeMove(Board board) {
        return 0;
    }

}
