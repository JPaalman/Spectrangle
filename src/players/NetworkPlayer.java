package group92.spectrangle.players;

import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Server;

public class NetworkPlayer extends Player {


    //creates a network player with a connectedClient and a name, only used from the server side
    //@ requires name != null && !name.contains(";") && connectedClient != null;
    //@ ensures getName() == name && connectedClient != null;
    public NetworkPlayer(String name) throws IllegalNameException {
        super(name);
    }

    //creates a network player, only used from the client side
    public NetworkPlayer() {
    }
}
