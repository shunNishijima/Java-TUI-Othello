package othello.model.game;

/**
 * storing Mark and index of location.
 * It is related to the OthelloGame which uses OthelloMove to make the real move on the board.
 */
public class OthelloMove implements Move{
    private Mark mark;
    private final int location;

    /**
     * Constructor
     * @param mark is mark
     * @param location index of place
     */
    /*@
       requires mark!=null&&64>location&&location>=0;
     */

    public OthelloMove(Mark mark,int location){
        this.mark = mark;
        this.location = location;
    }
    /**
     * Make a move to board
     * @param mark is Black or WHITE
     */
    /*@
       requires mark==Mark.BLACK||mark==Mark.WHITE;
       ensures this.mark == mark;
    */
    @Override
    public void setMark(Mark mark) {
        this.mark = mark;
    }

    /**
     * Thi is a getter of this move
     * @return mark which is set in this move.
     */
    /*@
        ensures \result==Mark.BLACK||\result==Mark.WHITE;
    */
    public Mark getMark() {
        return this.mark;
    }

    /**
     * This is getter for location of this move.
     * @return index number of this move.
     */
    /*@
        ensures \result<64||\result>=0;
    */
    public int getLocation() {
        return this.location;
    }
}
