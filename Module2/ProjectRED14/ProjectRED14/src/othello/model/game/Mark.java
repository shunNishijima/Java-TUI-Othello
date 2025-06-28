package othello.model.game;

/**
 * Represents a mark in the Othello game. There three possible values:
 * Mark.BLACK, Mark.WHITE and Mark.EMPTY.
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
