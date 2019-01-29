package group92.spectrangle.strategies;

import group92.spectrangle.board.Move;

import java.util.List;

public interface Strategy {

    Move getMove(List<Move> moves);

}
