package othello.model.game;
/**
 * This is the abstraction of Player.
 * Defining common using methods which are determining move, getter for mark and name.
 * This is related to OthelloGame which uses two Players for starting the game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;
    private final Mark mark;

    /**
     * Creates a new Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    /*@
        ensures \result==this.name;
        pure;
    */
    public String getName() {
        return this.name;
    }

    /**
     * Determines the next move, if the game still has available moves.
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameOver();
    //@ ensures game.isValidMove(\result);
    @Override
    public abstract Move determineMove(Game game);

    /**
     * Returns a representation of a player, i.e., their name
     * @return the String representation of this object
     */
    public String toString() {
        return "Player: " + name;
    }

    /**
     * getter for the mark
     * @return which mark this player have.
     */
    public Mark getMark() {
        return mark;
    }
}
