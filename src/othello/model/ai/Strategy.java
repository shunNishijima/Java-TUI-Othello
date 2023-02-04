package othello.model.ai;
import othello.model.game.Game;
import othello.model.game.Move;

/**
 * As an interface of strategy, it provides common command for strategy.
 */
public interface Strategy {
    /**
     * getter for the name of this strategy
     * @return name as string
     */
    String getName();

    /**
     * method perform how this strategy determine good choice of move.
     * @param game game which this strategy work.
     * @return good determined move.
     */
    Move determineMove(Game game);
}
