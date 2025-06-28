package othello.model.ai;

import othello.model.game.Game;
import othello.model.game.Move;
import othello.model.game.Mark;

public interface Strategy {
    String getName();
    Move determineMove(Game game);
}
