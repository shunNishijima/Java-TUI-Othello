package othello.model.game;
/**
 * as interface, define general commands for a board game.
 */
public interface Player {
    Move determineMove(Game game);
}
