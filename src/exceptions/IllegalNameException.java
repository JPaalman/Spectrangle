package group92.spectrangle.exceptions;

public class IllegalNameException extends Exception {

    //throws an illegal name exception
    //@ requires message != null;
    public IllegalNameException(String message) {
        super(message);
    }
}
