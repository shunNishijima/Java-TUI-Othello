package othello.model.game;
import java.util.ArrayList;
import java.util.List;

/**
 * implement game logic of Othello game.
 */

public class OthelloGame implements Game{

    //@public invariant !isGameOver()==>getValidMoves().size()>0;
    //@public invariant !isGameOver()==>getWinner()==null;
    //@public invariant !isGameOver()==>getTurn()!=null;

    public Board board;
    private final Player player1;
    private final Player player2;
    private Mark mark = Mark.BLACK;

    /**
     * Simple Constructor for making new game by getting 2 player
     * @param player1 input Computer or Human player
     * @param player2 input Computer or Human player
     */
    /*@
        requires player1!=null && player2 !=null;
        ensures board!=null;
    */
    public OthelloGame(Player player1,Player player2){
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
    }
    /**
     * Check if the game is over, means neither player can place a disc that captures discs of the opponent.
     * @return whether the game is over
     */
    /*@
        pure
    */
    @Override
    public boolean isGameOver() {
        //check if valid moves of this mark is nothing.
        boolean over = getValidMoves().isEmpty();
        switchTurn();
        //check if valid moves of other mark is nothing.
        over = over&&getValidMoves().isEmpty();
        switchTurn(); //make turn as same as before
        return over;
    }

    /**
     * Query whose turn it is. begin with mark is Black=player1. return which mark now is.
     * @return the player whose turn it is
     */
    /*@
        requires this.mark!=mark.EMPTY;
        ensures \result==player1||\result==player2;
        pure;
    */
    @Override
    public Player getTurn() {
        if(this.mark==Mark.BLACK){
            return player1;
        }else {
            return player2;
        }
    }

    /**
     * this method is used for changing turn in the game.
     */
    /*@
        ensures this.mark!=\old(this.mark);
    */
    public void switchTurn(){
        this.mark=this.mark.other();
    }

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     * @return the winner, or null if no player is the winner
     */
    /*@
        requires isGameOver();
        pure;
    */
    @Override
    public Player getWinner() {
        if (isGameOver()) {
            int black = 0;
            int white = 0;
            for (int i = 0; i < Board.DIM * Board.DIM; i++) {
                if (board.getField(i) == Mark.BLACK) {
                    black++;
                } else if (board.getField(i) == Mark.WHITE) {
                    white++;
                }
            }
            if (black > white) {
                return player1;
            } else if (white > black) {
                return player2;
            } else {
                return null;
            }
        }
        return null;
    }

    /**
     * Return all moves that are valid in the current state of the game.
     * player1 use Mark BLACK and player2 use Mark WHITE.
     * @return the list of currently valid moves
     */
    /*@
        ensures \result instanceof OthelloMove||\result.isEmpty();
        ensures (\forall Move m; \result.contains(m); isValidMove(m));
        pure;
    */
    @Override
    public List<Move> getValidMoves() {
        List<Move> moves = new ArrayList<>();
        if(getTurn()==player1){
            for(int i=0;i<Board.DIM*Board.DIM;i++){
                OthelloMove othelloMove = new OthelloMove(Mark.BLACK,i);
                if(isValidMove(othelloMove)){
                    moves.add(othelloMove);
                }
            }
        }else {
            for(int i=0;i<Board.DIM*Board.DIM;i++){
                OthelloMove othelloMove = new OthelloMove(Mark.WHITE,i);
                if(isValidMove(othelloMove)){
                    moves.add(othelloMove);
                }
            }
        }
        return moves;
    }

    /**
     * Check if a move is a valid move, which is at least one closest area has other Mark,
     * And on this line, there is mark itself next to other Mark.
     * @param move the move to check
     * @return true if the move is a valid move
     */
    /*@
        requires move!=null;
        ensures \result==true||\result==false;
        ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
        pure;
    */
    @Override
    public boolean isValidMove(Move move) {
        //check field location already has mark.
        if(!board.isEmptyField(((OthelloMove)move).getLocation())){
            return false;
        }
        //Check if this move is valid for above.
        if(!(((OthelloMove) move).getLocation()<9)){
            //Check if there is other mark next above from the location.
            if(board.getField(((OthelloMove) move).getLocation()-8)==mark.other()){
                //Check there is own mark after sequence of other mark above.
                for(int i=((OthelloMove) move).getLocation()-8;i>=0;i=i-8){
                    if(board.isEmptyField(i)){
                        break;
                    } else if (board.getField(i)==mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for below.
        if (!(((OthelloMove) move).getLocation()>55)) {
            //Check if there is other mark next below from the location.
            if(board.getField(((OthelloMove) move).getLocation()+8)==mark.other()) {
                //Check there is own mark after sequence of other mark below.
                for (int i = ((OthelloMove) move).getLocation()+8; i <64; i = i+8) {
                    if (board.isEmptyField(i)) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for left.
        if (!(((OthelloMove) move).getLocation()%8==0)) {
            //Check if there is other mark next left from the location.
            if(board.getField(((OthelloMove) move).getLocation()-1)==mark.other()) {
                //Check there is own mark after sequence of other mark left.
                for (int i = ((OthelloMove) move).getLocation() - 1; i%8!=7; i--) {
                    if (board.getField(i) == Mark.EMPTY) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for right.
        if (!(((OthelloMove) move).getLocation()%8==7)) {
            //Check if there is other mark next right from the location.
            if(board.getField(((OthelloMove) move).getLocation()+1)==mark.other()) {
                //Check there is own mark after sequence of other mark right.
                for (int i = (((OthelloMove) move).getLocation() + 1); i%8!=0; i++) {
                    if (board.getField(i) == Mark.EMPTY) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for right and up diagonal.
        if (!(((OthelloMove) move).getLocation()%8==7)&&!(((OthelloMove) move).getLocation()<9)) {
            //Check if there is other mark next right and up diagonal from the location.
            if(board.getField(((OthelloMove) move).getLocation()-7)==mark.other()) {
                //Check there is own mark after sequence of other mark right and up diagonal.
                for (int i = (((OthelloMove) move).getLocation()-7);i%8!=0&&i>=0;i=i-7) {
                    if (board.getField(i) == Mark.EMPTY) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for right and down diagonal.
        if (!(((OthelloMove) move).getLocation()%8==7)&&!(((OthelloMove) move).getLocation()>55)) {
            //Check if there is other mark next right and down diagonal from the location.
            if(board.getField(((OthelloMove) move).getLocation()+9)==mark.other()) {
                //Check there is own mark after sequence of other mark right and down diagonal.
                for (int i = (((OthelloMove) move).getLocation()+9);i%8!=0&&i<64;i=i+9) {
                    if (board.getField(i) == Mark.EMPTY) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for left and up diagonal.
        if (!(((OthelloMove) move).getLocation()%8==0)&&!(((OthelloMove) move).getLocation()<9)) {
            //Check if there is other mark next left and up diagonal from the location.
            if(board.getField(((OthelloMove) move).getLocation()-9)==mark.other()) {
                //Check there is own mark after sequence of other mark left and up diagonal.
                for (int i = (((OthelloMove) move).getLocation()-9);i%8!=7&&i>=0;i=i-9) {
                    if (board.getField(i) == Mark.EMPTY) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        //Check if this move is valid for left and down diagonal.
        if (!(((OthelloMove) move).getLocation()%8==0)&&!(((OthelloMove) move).getLocation()>55)) {
            //Check if there is other mark next left and down diagonal from the location.
            if(board.getField(((OthelloMove) move).getLocation()+7)==mark.other()) {
                //Check there is own mark after sequence of other mark left and down diagonal.
                for (int i = (((OthelloMove) move).getLocation()+7);i%8!=7&&i<64;i=i+7) {
                    if (board.isEmptyField(i)) {
                        break;
                    } else if (board.getField(i) == mark) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * Perform the move, assuming it is a valid move.
     * capture every other mark which is necessary to be turned using set field method.
     * @param move the move to play
     */
    /*@
        requires isValidMove(move);
    */
    @Override
    public void doMove(Move move) {
        if (isValidMove(move)) {
            //set mark on the location.
            board.setField(((OthelloMove) move).getLocation(), ((OthelloMove) move).getMark());
            if (!(((OthelloMove) move).getLocation()<9)) {
                //check if other mark is on next to location above.
                if (board.getField(((OthelloMove) move).getLocation()-8) == mark.other()) {
                    //capture other mark until top by reach to own mark.
                    for (int i = ((OthelloMove) move).getLocation()-8; i >= 0; i = i-8) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for(int j = i+8;j<((OthelloMove) move).getLocation();j=j+8){
                                board.setField(j, mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()>55)) {
                //check if other mark is on next to location below.
                if (board.getField(((OthelloMove) move).getLocation() + 8) == mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = ((OthelloMove) move).getLocation() + 8; i < 64; i = i + 8) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for(int j=i-8;j>((OthelloMove) move).getLocation();j=j-8){
                                board.setField(j, mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==0)) {
                //check if other mark is on next to location left.
                if (board.getField(((OthelloMove) move).getLocation() - 1) == mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = ((OthelloMove) move).getLocation() - 1; i % 8 != 7; i--) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i+1;j<((OthelloMove) move).getLocation();j++){
                                board.setField(j, mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==7)) {
                //check if other mark is on next to location right.
                if (board.getField(((OthelloMove) move).getLocation() + 1) == mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = ((OthelloMove) move).getLocation() + 1; i % 8 != 0; i++) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i-1;j>((OthelloMove) move).getLocation();j--){
                                board.setField(j, mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==7)&&!(((OthelloMove) move).getLocation()<9)) {
                //check if other mark is on next to location right up diagonal.
                if(board.getField(((OthelloMove) move).getLocation()-7)==mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = (((OthelloMove) move).getLocation()-7);i%8!=0&&i>=0;i=i-7) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i+7;j<((OthelloMove) move).getLocation();j=j+7){
                                board.setField(j,mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==7)&&!(((OthelloMove) move).getLocation()>55)) {
                //check if other mark is on next to location right down diagonal.
                if(board.getField(((OthelloMove) move).getLocation()+9)==mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = (((OthelloMove) move).getLocation()+9);i%8!=0&&i<64;i=i+9) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i-9;j>((OthelloMove) move).getLocation();j=j-9){
                                board.setField(j,mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==0)&&!(((OthelloMove) move).getLocation()<9)) {
                //check if other mark is on next to location left up diagonal.
                if(board.getField(((OthelloMove) move).getLocation()-9)==mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = (((OthelloMove) move).getLocation()-9);i%8!=7&&i>=0;i=i-9) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i+9;j<((OthelloMove) move).getLocation();j=j+9){
                                board.setField(j,mark);
                            }
                        }
                    }
                }
            }
            if (!(((OthelloMove) move).getLocation()%8==0)&&!(((OthelloMove) move).getLocation()>55)) {
                //check if other mark is on next to location left down diagonal.
                if(board.getField(((OthelloMove) move).getLocation()+7)==mark.other()) {
                    //capture other mark until bottom by reach to own mark.
                    for (int i = (((OthelloMove) move).getLocation()+7);i%8!=7&&i<64;i=i+7) {
                        if (board.getField(i) == Mark.EMPTY) {
                            break;
                        } else if (board.getField(i) == mark) {
                            for (int j=i-7;j>((OthelloMove) move).getLocation();j=j-7){
                                board.setField(j,mark);
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * set board for this game using for deep copy.
     * @param board probably deep copy of the board.
     */
    public void setBoard(Board board){
        this.board = board;
    }
}
