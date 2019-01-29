package group92.spectrangle.strategies;

import group92.spectrangle.board.Move;

import java.util.List;

public class RandomStrategy implements Strategy {

    @Override
    public Move getMove(List<Move> moves) {
        return moves.get((int) (Math.random() * moves.size()));
    }

}