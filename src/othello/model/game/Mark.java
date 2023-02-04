package othello.model.game;

/**
 * Defining a variety of marks as EMPTY, BLACK, WHITE. Has other method to return the mark.
 * This is used in whole game classes.
 */
public enum Mark {
    EMPTY, WHITE, BLACK;

    /**
     * Returns the other mark.
     * @return the other mark is this mark is not EMPTY or EMPTY
     */
    //@ ensures this == WHITE ==> \result == BLACK && this == BLACK ==> \result == WHITE;
    public Mark other() {
        if (this == WHITE) {
            return BLACK;
        } else if (this == BLACK) {
            return WHITE;
        } else {
            return EMPTY;
        }
    }

}
