package group92.spectrangle.board;

import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.view.GUI;

import java.util.Observable;

public class Field extends Observable {

    // TODO improve Observer

    private int multiplier;

    private Tile tile;

    public Field(int multiplier) {
        this.multiplier = multiplier;
//        addObserver(GUI.get());
    }

    public Tile getTile() {
        return tile;
    }

    public int place(Tile tile) throws MoveException {
        if (this.tile == null) {
            this.tile = tile;
            setChanged();
            notifyObservers();
            return tile.getMultiplier() * multiplier;
        } else {
            throw new MoveException("field is not empty");
        }
    }

}