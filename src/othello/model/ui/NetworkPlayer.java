package othello.model.ui;
import othello.model.game.*;

/**
 * As extension of Abstract Player, it determines move by Protocol messages created by user input.
 * The player can work with a client in an environment connected with the network.
 * It is possible to receive a Protocol message to determine move.
 */
public class NetworkPlayer extends AbstractPlayer {
    private final Mark mark;
    private int location;
    /**
     * Creates a new Player object.
     * @param mark mark of this player
     * @param name name of client who plays
     */
    public NetworkPlayer(Mark mark,String name) {
        super(name, mark);
        this.mark = mark;
    }

    /**
     * Determines the next move, if the game still has available moves.
     * getting move by input from user
     * @param game the current game
     * @return the player's choice
     */
    @Override
    public Move determineMove(Game game) {
        return new OthelloMove(this.getMark(), this.location);
    }

    /**
     * getter for this mark
     * @return mark of this player
     */
    public Mark getMark() {
        return mark;
    }

    /**
     * set the location Protocol messages from user input.
     * @param i index for next move.
     */
    public void setLocation(int i){
        this.location = i;
    }
}
