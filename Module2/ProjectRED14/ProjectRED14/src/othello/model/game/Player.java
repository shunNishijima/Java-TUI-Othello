package othello.model.game;

/**
 * A player of a turn-based game.
 */
public interface Player {
    Move determineMove(Game game);
}
