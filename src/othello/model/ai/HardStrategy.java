package othello.model.ai;
import othello.model.game.*;

/**
 * As implementation of Strategy, determines move automatically.
 * This strategy is a high level strategy.
 * It provides the best move for the game at that time to a computer player.
 */
public class HardStrategy extends EasyStrategy implements Strategy{
    private final Util util = new Util();

    /**
     * Game mode name getter
     * @return "Hard Mode"
     */
    @Override
    public String getName() {
        return "Hard Mode";
    }

    /**
     * Determines the best move by using the bestMove() function
     *
     * @param game the current game
     * @return the "best" move for the computer player
     */
    @Override
    public Move determineMove(Game game) {
        OthelloGame othelloGame = (OthelloGame)game;
        Move[] moves = othelloGame.getValidMovesArray();
        return bestMove(moves, othelloGame.gameDeepCopy());
    }

    /**
     * The function tries to determine the best move by looking which one will give the opponent least possibilities next turn
     * and then checking it against pre-determined lists of "good" and "bad" moves
     * @param moves list of currently valid moves
     * @param game deep copy of the current game
     * @return the move with lowest "rank"
     */
    public Move bestMove(Move[] moves, OthelloGame game) {
        int i = 0;
        int l = moves.length;
        //System.out.println(l);
        int[] rank = new int[l];
            while (i < (l/2)) {
                OthelloMove cmove = (OthelloMove) (moves[i]);
                final Board resetBoard = game.getBoard().deepCopy();
                game.doMove(cmove);
                game.switchTurn();
                Move[] opponentMoves = game.getValidMovesArray();
                int j = 0;
                for (Move move : opponentMoves) {
                    final Board resetOpponentBoard = game.getBoard().deepCopy();
                    game.doMove(move);
                    j = j + game.getBoard().countPieces(((OthelloMove) move).getMark());
                    game.setBoard(resetOpponentBoard);

                }
                if (opponentMoves.length != 0) {
                    rank[i] = j / (opponentMoves.length);
                }
                game.setBoard(resetBoard);
                i++;
            }
            return moves[util.getSmallestIntIndex(rank)];
    }
}
