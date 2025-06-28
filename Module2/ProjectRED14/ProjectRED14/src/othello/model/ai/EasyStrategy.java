package othello.model.ai;

import othello.model.game.Game;
import othello.model.game.Move;

import java.util.List;

public class EasyStrategy implements Strategy{
    private final String name = "Easy Mode";
    private List<Move> moves;

    /**
     * Game mode name getter
     * @return "Easy Mode"
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Determines the next move by choosing a random one from the list of valid ones
     *
     * @param game the current game
     * @return a random valid move
     */
    @Override
    public Move determineMove(Game game) {
        moves = game.getValidMoves();
        return moves.get((int)(Math.random() * ((moves.size()))));
    }
}
