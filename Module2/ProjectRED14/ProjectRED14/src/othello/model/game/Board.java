package othello.model.game;

/**
 * Board for the Tic Tac Toe game.
 */
public class Board {
    /**
     * Dimension of the board, i.e., if set to 3, the board has 3 rows and 3 columns.
     */
    public static final int DIM = 8;
    private static final String DELIM = "     ";
    /**
     * The DIM by DIM fields of the Othello board. See NUMBERING for the
     * coding of the fields.
     */
    private static final String[] NUMBERING = {
            " A1 | B1 | C1 | D1 | E1 | F1 | G1 | H1 ",
            "----+----+----+----+----+----+----+----",
            " A2 | B2 | C2 | D2 | E2 | F2 | G2 | H2 ",
            "----+----+----+----+----+----+----+----",
            " A3 | B3 | C3 | D3 | E3 | F3 | G3 | H3 ",
            "----+----+----+----+----+----+----+----",
            " A4 | B4 | C4 | D4 | E4 | F4 | G4 | H4 ",
            "----+----+----+----+----+----+----+----",
            " A5 | B5 | C5 | D5 | E5 | F5 | G5 | H5 ",
            "----+----+----+----+----+----+----+----",
            " A6 | B6 | C6 | D6 | E6 | F6 | G6 | H6 ",
            "----+----+----+----+----+----+----+----",
            " A7 | B7 | C7 | D7 | E7 | F7 | G7 | H7 ",
            "----+----+----+----+----+----+----+----",
            " A8 | B8 | C8 | D8 | E8 | F8 | G8 | H8 ",
    };
    private static final String LINE = NUMBERING[1];
    private Util util = new Util();
    private Mark[] fields;

    /**
     * Constructor Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public Board() {
        fields = new Mark[DIM*DIM];
        for(int i = 0;i<DIM*DIM;i++){
            if (i==Util.calculateField("D4") || i == util.calculateField("E5")){
                fields[i] = Mark.WHITE;
            } else if (i== util.calculateField("E4") || i == util.calculateField("D5")) {
                fields[i] = Mark.BLACK;
            }
            else {
                fields[i] = Mark.EMPTY;
            }
        }
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board deepCopy = new Board();
        deepCopy.fields = new Mark[DIM*DIM];
        for(int i=0;i<DIM*DIM;i++){
            deepCopy.fields[i] = this.fields[i];
        }
         return deepCopy;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM;
    requires col >= 0 && row < DIM;
     @*/
    public int index(int row, int col) {
        return row*DIM + col;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures index >= 0 && index < DIM*DIM ==> \result == true;
    //@pure;
    public boolean isField(int index) {
        return index >= 0 && index < DIM * DIM;
    }

    /**
     * Returns true of the (row,col) pair refers to a valid field on the board.
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    //@ pure;
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the content of the field i.
     * @param i the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    /*@ requires isField(i);
    ensures \result == Mark.EMPTY || \result == Mark.BLACK || \result == Mark.WHITE;
     @*/
    //@ pure;
    public Mark getField(int i) {
        if(isField(i)){
            return this.fields[i];
        }
         return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY || \result == Mark.BLACK || \result == Mark.WHITE;
     @*/
    //@ pure;
    public Mark getField(int row, int col) {
        if (isField(row, col)) {
            return this.fields[index(row,col)];
        } else {
            return null;
        }
    }

    /**
     * Returns true if the field i is empty.
     * @param i the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    /*@ requires isField(i)==true;
    ensures getField(i) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int i) {
        return getField(i) == Mark.EMPTY;
    }

    /**
     * Returns true if the field i is empty. Using set of alphabet and number like A1. This is used for Test only.
     * @param c column
     * @param r row
     * @return true if the field is empty.
     */
    /*@
        requires isField(util.calculateField(""+c+r))==true;
        ensures getField(util.calculateField(""+c+r)) == Mark.EMPTY ==> \result==true;
    */
    public boolean isEmptyField(Character c, int r)
    {
        return getField(util.calculateField(""+c +r)) == Mark.EMPTY;
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                row += " " + getField(i, j).toString().substring(0, 1).replace("E", " ") + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row + DELIM + NUMBERING[i * 2];
            if (i < DIM - 1) {
                s = s + "\n" + LINE + DELIM + NUMBERING[i * 2 + 1] + "\n";
            }
        }
        return s;
    }

    /**
     * Sets the content of field i to the mark m.
     * @param i the field number (see NUMBERING)
     * @param m the mark to be placed
     */
    /*@ requires isField(i);
    ensures getField(i) == m;
     @*/
    public void setField(int i, Mark m) {
        if(isField(i)){
            fields[i] = m;
        }
    }

    /** sets the field based on row and column by translating them into an index integer
     *
     * @param c column
     * @param r row
     * @param m mark
     */

    public void setField(char c , int r, Mark m) {
        if(isField(util.calculateField(""+c+r))){
            fields[util.calculateField(""+c+r)] = m;
        }
    }

    /** counts the number of the pieces of both colors on the board at the moment
     *
     *@return [white pieces, black pieces]
     */

    public int[] countPieces() {
        int whiteCounter = 0;
        int blackCounter = 0;
        for (int i = 0;i<64;i++) {
            if(this.getField(i).equals(Mark.WHITE)) {
                whiteCounter++;
            } else if (this.getField(i).equals(Mark.BLACK)) {
                blackCounter++;
            }

        }
        int[] arr = {whiteCounter,blackCounter};
        return arr;
    }

}
