package othello.model.ui;
import othello.model.game.*;
import java.util.Scanner;

/**
 * Player as Human Player which is input from user based player.
 */

public class HumanPlayer extends AbstractPlayer {
    /**
     * Creates a new Player object.
     */
    /*@
        requires name!=null;
    */
    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Determines the next move, if the game still has available moves.
     * @param game the current game
     * @return the player's choice
     */
    /*@
        requires game!=null;
        ensures \result==null||game.isValidMove(\result);
    */
    @Override
    public Move determineMove(Game game) {
        Scanner scanner = new Scanner(System.in);
        System.out.println("Enter your move "+getName()+" : ");
        Move move = makeMove(scanner);
        while(move==null||!game.isValidMove(move)){
            System.out.println("Invalid. Put it again: \n");
            System.out.println(((OthelloGame) game).board.toString());
            move = makeMove(scanner);
        }
        return move;
    }

    /**
     * To determine move, getting input from System and split which color and index.
     * @param input getting input from system input.
     * @return return constructed othello move which has index number of location.
     */
    /*@
        requires input!=null;
        ensures input==null ==> \result==null&& \result instanceof OthelloMove;
    */
    public Move makeMove(Scanner input) {
        String command = input.nextLine();
        String[] split = command.split(" ");

        switch (split[0]) {
            case "B":
                return new OthelloMove(Mark.BLACK, Util.calculateField(split[1]));
            case "W":
                return new OthelloMove(Mark.WHITE, Util.calculateField(split[1]));
            default:
                return null;
        }
    }
}
