package group92.spectrangle.players;

import group92.spectrangle.board.Board;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.strategies.SimpleStrategy;

public class ComputerPlayer extends Player {
    private SimpleStrategy strategy;

    //Constructs a computer player with a strategy
    //@ requires name != null && strategy != null;
    //@ ensures getName() == name;
    public ComputerPlayer(String name, SimpleStrategy strategy) throws IllegalNameException {
        super(name + " [bot]");
        this.strategy = strategy;
    }

    //Makes a move using the strategy of this computer player
    //@ requires board != null;
    @Override
    public int makeMove(Board board) {
        if(board != null) {
            return strategy.makeMove(board);
        } else {
            return 0;
        }
    }
}
