package group92.spectrangle.board;

public class Board {

    private Tile[] tiles;

    public Board() {
        tiles = new Tile[36];
        for (int i = 0; i < 36; i++) {
            if (i == 0) {
                // TODO multiplicity 4
            } else if (i == 1) {
                // TODO multiplicity 2
            } else {
                tiles[i] = new Tile(1);
            }
        }

    }

    private class Tile {

        private int multiplier;

        private Piece piece;

        public Tile(int multiplier) {
            this.multiplier = multiplier;
        }

        // TODO check if (multiple) sides align
        // TODO improve exception handling
        public int place(Piece piece) throws Exception {
            if (this.piece == null) {
                this.piece = piece;
                return piece.getMultiplier() * multiplier;
            }
            throw new Exception("shit does not work, yo");
        }

    }

}
