package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.network.Client;
import group92.spectrangle.view.GUI;

public class ClientPlayer extends Player {
    private GUI gui;
    private Client client;

    public ClientPlayer(String name) throws IllegalNameException {
        super(name);
    }
}
