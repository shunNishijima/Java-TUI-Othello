package othello.model;
import othello.model.game.Board;
import othello.model.game.Mark;
// maybe can be done better

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;


public class BoardTest {
    private Board board;

    // makes a new board
    @BeforeEach
    public void setUp() {
        board = new Board();
    }


    /**
     * tests whether the indexing of board tiles is in order
     */
    @Test
    public void testIndex() {
        int index = 0;
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(index, board.index(i, j));
                index += 1;
            }
        }
        assertEquals(0, board.index(0, 0));
        assertEquals(1, board.index(0, 1));
        assertEquals(8, board.index(1, 0));
        assertEquals(18, board.index(2, 2));
    }


    /**
     * tests if the "board" is contained within the set dimensions/indexes
     */
    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.DIM * Board.DIM - 1));
        assertFalse(board.isField(Board.DIM * Board.DIM));
    }


    /**
     * tests if the "board" is contained within the set dimensions/indexes
     * using row+column input
     */
    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertFalse(board.isField(9, 1));
        assertFalse(board.isField(1, 9));
    }

    /**
     * test if setting a field to a specified mark works
     */

    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Mark.WHITE);
        board.setField(40, Mark.BLACK);
        assertEquals(Mark.WHITE, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(1));
        assertEquals(Mark.BLACK, board.getField(40));
    }

    /**
     * test if setting a field to a specified mark works
     * using row + column input
     */
    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField('A', 1, Mark.BLACK);
        assertEquals(Mark.BLACK, board.getField(0, 0));
        assertEquals(Mark.EMPTY, board.getField(0, 1));
        assertEquals(Mark.EMPTY, board.getField(1, 0));
        assertEquals(Mark.EMPTY, board.getField(1, 1));
    }

    /**
     * test if the board was created correctly for the other tests
     */
    @Test
    public void testSetup() {
        for (int i = 0; i < Board.DIM * Board.DIM; i++)
        if(i == 27 || i == 36)
        {
            assertEquals(Mark.WHITE, board.getField(i));
        }
        else if(i == 28 || i == 35)
        {
            assertEquals(Mark.BLACK, board.getField(i));
        }
        else
        {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
    }

    /**
     * test if the deepCopy() function creates a true copy of the board
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, Mark.WHITE);
        board.setField(Board.DIM * Board.DIM - 1, Mark.BLACK);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

        // Check if a field in the deepcopied board the original remains the same
        deepCopyBoard.setField(0, Mark.BLACK);

        assertEquals(Mark.WHITE, board.getField(0));
        assertEquals(Mark.BLACK, deepCopyBoard.getField(0));
    }

    /**
     * tests if the isEmptyField() function can detect empty fields correctly
     */
    @Test
    public void testIsEmptyFieldIndex() {
        board.setField(0, Mark.WHITE);
        assertFalse(board.isEmptyField(0));
        assertTrue(board.isEmptyField(1));
    }

    /**
     * tests if the isEmptyField() function can detect empty fields correctly
     * using row + column input
     */

    @Test
    public void testIsEmptyFieldRowCol() {
        board.setField('A', 0, Mark.WHITE);
        assertFalse(board.isEmptyField('A', 0));
        assertTrue(board.isEmptyField('A', 1));
        assertTrue(board.isEmptyField('B', 1));
    }


}
