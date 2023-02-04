package othello.model.ui;
import othello.model.game.*;
import java.util.Scanner;

/**
 * As extension of Abstract Player, it determines move according to user input from user interface.
 * Players work from user input in an environment without a network. Workable only by input from the user interface.
 */

public class HumanPlayer extends AbstractPlayer {
    private final Util util = new Util();
    /**
     * Creates a new Player object.
     */
    /*@
        requires name!=null;
    */
    public HumanPlayer(String name,Mark mark) {
        super(name, mark);
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
                return new OthelloMove(Mark.BLACK, util.calculateField(split[1]));
            case "W":
                return new OthelloMove(Mark.WHITE, util.calculateField(split[1]));
            default:
                return null;
        }
    }
}
