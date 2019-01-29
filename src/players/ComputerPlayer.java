package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Move;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.strategies.SimpleStrategy;
import group92.spectrangle.strategies.Strategy;

import java.util.ArrayList;

public class ComputerPlayer extends Player {

    private Strategy strategy;

    //Constructs a computer player with a strategy
    //@ requires name != null && strategy != null && !name.contains(";");
    //@ ensures getName() == name;
    public ComputerPlayer(String name, Strategy strategy) throws IllegalNameException {
        super(name + " [bot]");
        this.strategy = strategy;
    }

    public ComputerPlayer() {
        this(new SimpleStrategy());
    }

    public ComputerPlayer(Strategy strategy) {
        super();
        this.strategy = strategy;
    }

    public ComputerPlayer(String name) throws IllegalNameException {
        this(name, new SimpleStrategy());
    }

    public String getMove(Board board) {
        ArrayList<Move> possibleMoves = new ArrayList<>();
        for (Tile tile : getInventory()) {
            int[][] indices = board.getPossibleFields(tile);
            for (int i = 0; i < indices.length; i++) {
                for (int j = 0; j < indices[i].length; i++) {
                    possibleMoves.add(new Move(tile, indices[i][j]));
                }
            }
        }
        return strategy.getMove(possibleMoves).toString();
    }

}
