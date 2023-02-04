package othello.model.game;

/**
 *  as an interface, it defines the usual method for a board game.
 */
public interface Move {
    /**
     * Make a move to board
     * @param mark is Black or WHITE
     */
    void setMark(Mark mark);
}
