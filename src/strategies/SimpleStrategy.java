package group92.spectrangle.strategies;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Move;

import java.util.ArrayList;
import java.util.List;

public class SimpleStrategy implements Strategy {

    public Move getMove(List<Move> moves) {
        // get a list of moves with the highest available field multiplier
        System.out.println("processing " + moves.size() + " moves");
        if (moves.size() == 0) {
            return null;
        }
        ArrayList<Move> temp = new ArrayList<>();
        for (Move move : moves) {
            if (Board.MULTIPLICITY_4.contains(move.getIndex())) {
                temp.add(move);
            }
        }
        if (temp.isEmpty()) {
            for (Move move : moves) {
                if (Board.MULTIPLICITY_3.contains(move.getIndex())) {
                    temp.add(move);
                }
            }
            if (temp.isEmpty()) {
                for (Move move : moves) {
                    if (Board.MULTIPLICITY_2.contains(move.getIndex())) {
                        temp.add(move);
                    }
                }
                if (temp.isEmpty()) {
                    for (Move move : moves) {
                        temp.add(move);
                    }
                }
            }
        }

        // get the first move from temp, replace if a better move is found
        Move result = null;
        for (Move move : temp) {
            if (result == null || move.getTile().getMultiplier() > result.getTile().getMultiplier()) {
                result = move;
            }
        }
        return result;
    }

}
