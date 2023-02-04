package othello.model.ai;
import othello.model.game.Game;
import othello.model.game.Move;
import java.util.List;

/**
 * Implementation of Strategy, determines move automatically.
 * This strategy is a low level strategy, so it provides a random valid move to a computer player.
 */
public class EasyStrategy implements Strategy{
    /**
     * Game mode name getter
     * @return "Easy Mode"
     */
    @Override
    public String getName() {
        return "Easy Mode";
    }

    /**
     * Determines the next move by choosing a random one from the list of valid ones
     *
     * @param game the current game
     * @return a random valid move
     */
    @Override
    public Move determineMove(Game game) {
        List<Move> moves = game.getValidMoves();
        return moves.get((int)(Math.random() * ((moves.size()))));
    }
}
