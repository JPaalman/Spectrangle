package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Server;

public class NetworkPlayer extends Player {

    private Server.ConnectedClient connectedClient;

    public NetworkPlayer(String name, Server.ConnectedClient connectedClient) throws IllegalNameException {
        super(name);
        this.connectedClient = connectedClient;
    }

    public Server.ConnectedClient getConnectedClient() {
        return connectedClient;
    }

    @Override
    public int makeMove(Board board) {
        return 0;
    }

}
