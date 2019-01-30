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
        super(name);
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
            for (int i = 0; i < 3; i++) {
                int[] indices = board.getPossibleFields(tile);
                for (int index : indices) {
                    possibleMoves.add(new Move(tile, index, i));
                }
                tile.rotate(1);
            }
        }
        Move result = strategy.getMove(possibleMoves);
        if (result != null) {
            return result.toString();
        }
        return "skip";
    }

}
