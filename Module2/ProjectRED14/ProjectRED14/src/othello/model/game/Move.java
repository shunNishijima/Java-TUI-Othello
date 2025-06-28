package othello.model.game;

/**
 * A move in a turn-based game.
 */
public interface Move {
    /**
     * Make a move to board
     * @param mark is Black or WHITE
     */
    void setMark(Mark mark);
}
