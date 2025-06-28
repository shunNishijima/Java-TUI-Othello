package othello.model.ai;

import othello.model.game.*;

import java.util.Arrays;
import java.util.List;

public class HardStrategy implements Strategy{
    private final String name = "Hard Mode";
    private List<Move> moves;
    private Util util = new Util();

    // list of tiles you usually want to avoid
    private final List<Integer> badMoves =  Arrays.asList(9, 10, 11, 12, 13, 14, 17, 25, 33, 41, 49, 50, 51, 52, 53, 54, 46, 38, 30, 22);

    // list of tiles you usually want to aim for
    private final List<Integer> goodMoves = Arrays.asList(0,8,16,24,32,40,48,56, 57, 58, 59, 60, 61, 62, 63, 7, 15, 23, 31, 39, 47, 55, 1, 2, 3, 4, 5, 6);

    /**
     * Game mode name getter
     * @return "Hard Mode"
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Determines the best move by using the bestMove() function
     *
     * @param game the current game
     * @return the "best" move for the computer player
     */
    public Move determineMove(Game game) {
        moves = game.getValidMoves();
        return bestMove(moves);
    }

    /**
     * The function tries to determine the best move by checking it against pre-determined lists of "good" and "bad" moves
     * Still a work in progress
     * @param moves list of currently valid moves
     * @return the move with lowest "rank"
     */
    public Move bestMove(List<Move> moves)
    {

        int i = 0;
        int[] rank = new int[moves.size()];
        while (i < moves.size())
        {
            OthelloMove cmove = (OthelloMove)(moves.get(i));

            if (badMoves.contains(cmove.getLocation())){
                rank[i] = rank[i]+10;
            } else if (goodMoves.contains(cmove.getLocation())) {
                rank[i] = rank[i]-12;
            }
            i++;
        }

        return moves.get(util.getSmallestIntIndex(rank));
    }
}
