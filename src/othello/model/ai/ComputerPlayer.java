package othello.model.ai;
import othello.model.game.AbstractPlayer;
import othello.model.game.Game;
import othello.model.game.Move;
import othello.model.game.Mark;

/**
 * As an extension of AbstractPlayer, it determines move by calculation depending on strategy.
 * It is possible to work in an environment connected with a network.
 */
public class ComputerPlayer extends AbstractPlayer {
    private final Mark mark;
    private final Strategy strategy;

    /**
     * Creates a new AI Player object with a specified mark and strategy they should follow.
     *
     * @param mark being assigned to player
     * @param strategy being assigned to player
     *
     */
    public ComputerPlayer(Mark mark,Strategy strategy,String name) {
        super(name, mark);
        this.mark = mark;
        this.strategy = strategy;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the choice based on which difficulty mode was chosen
     */
    @Override
    public Move determineMove(Game game) {
        if(this.strategy instanceof EasyStrategy) {
            return this.strategy.determineMove(game);
        }
        else if (this.strategy instanceof HardStrategy) {
           return this.strategy.determineMove(game);
        }
        else{
            return null;
        }
    }

    /**
     * @return the mark assigned to the player
     */
    public Mark getMark() {
        return mark;
    }
}
