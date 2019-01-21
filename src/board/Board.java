package group92.spectrangle.board;

public class Board {

    private class Bag {

        public final Piece[] pieces = new Piece[]{};

        public Bag() {

        }

    }

    private class Tile {

        private int multiplier;

        private Piece piece;

        public Tile(int multiplier) {
            this.multiplier = multiplier;
        }

        public int place(Piece piece) throws Exception {
            if (this.piece == null) {
                this.piece = piece;
                return piece.getMultiplier() * multiplier;
            }
            throw new Exception("shit does not work, yo");
        }

    }


}
