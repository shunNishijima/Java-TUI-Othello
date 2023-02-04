package othello.model;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.model.game.*;
import othello.model.ui.HumanPlayer;
import java.util.List;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Test whole othello Game logic is implemented.
 * The Othello game should emulate all the logic and rules of the real board game without errors.
 */
public class OthelloGameTest {
    Player player1;
    Player player2;
    private Game game;

    /**
     * Setting up default game.
     */
    @BeforeEach
    public void setUp(){
        player1 = new HumanPlayer("p1",Mark.BLACK);
        player2 = new HumanPlayer("p2",Mark.WHITE);
        game = new OthelloGame(player1,player2);
    }

    /**
     * Check if Game over logic is working correctly
     */
    @Test
    public void TestGameOver(){
        //Check when every mark in field is Black.
        ((OthelloGame) game).board.setField(27, Mark.BLACK);
        ((OthelloGame) game).board.setField(36, Mark.BLACK);
        assertTrue(game.isGameOver());

        //Check all field has mark and game is over.
        for (int i=0;i<32;i++){
            ((OthelloGame) game).board.setField(i,Mark.BLACK);
        }
        for (int i=32;i<64;i++){
            ((OthelloGame) game).board.setField(i,Mark.WHITE);
        }
        assertTrue(game.isGameOver());
    }

    /**
     * Check if turn method work correctly.
     */
    @Test
    public void TestTurn(){
        assertEquals(game.getTurn(),player1);
        ((OthelloGame)game).switchTurn();
        assertEquals(game.getTurn(),player2);
    }

    /**
     * Test if winner is correctly got.
     */
    @Test
    public void TestGetWinner(){
        //every mark in the field is Black
        ((OthelloGame) game).board.setField(27, Mark.BLACK);
        ((OthelloGame) game).board.setField(36, Mark.BLACK);
        assertEquals(game.getWinner(),game.getTurn());

        //change as default which means there are no winner.
        ((OthelloGame) game).board.setField(27, Mark.WHITE);
        ((OthelloGame) game).board.setField(36, Mark.WHITE);
        assertNull(game.getWinner());

        //every mark in the field is White.
        ((OthelloGame) game).board.setField(28, Mark.WHITE);
        ((OthelloGame) game).board.setField(35, Mark.WHITE);
        ((OthelloGame) game).switchTurn();
        assertEquals(game.getWinner(),game.getTurn());

        //board is full of mark. and the number of black is more than white.
        for (int i=0;i<33;i++){
            ((OthelloGame) game).board.setField(i,Mark.BLACK);
        }
        for (int i=33;i<64;i++){
            ((OthelloGame) game).board.setField(i,Mark.WHITE);
        }
        assertEquals(game.getWinner(),player1);

        //number of mark is exactly same.
        for (int i=0;i<32;i++){
            ((OthelloGame) game).board.setField(i,Mark.BLACK);
        }
        for (int i=32;i<64;i++){
            ((OthelloGame) game).board.setField(i,Mark.WHITE);
        }
        assertNull(game.getWinner());

    }

    /**
     * Check if we can correctly get valid moves.
     */
    @Test
    public void TestValidMove(){
        //as default the number of valid moves must be 4 for black.
        List<Move> move = game.getValidMoves();
        assertEquals(move.size(),4);
        ((OthelloGame)game).switchTurn();
        //as default the number of valid moves must be 4 for white.
        move = game.getValidMoves();
        assertEquals(move.size(),4);
    }

    /**
     * Check move for both BLACK and WHITE works correctly.
     */
    @Test
    public void TestDoMove(){
        game.doMove(new OthelloMove(Mark.BLACK,26));
        game.doMove(new OthelloMove(Mark.WHITE,34));
        game.doMove(new OthelloMove(Mark.BLACK,42));
        game.doMove(new OthelloMove(Mark.WHITE,33));
    }

}
