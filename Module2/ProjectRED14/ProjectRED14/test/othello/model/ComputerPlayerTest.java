package othello.model;

import org.junit.jupiter.api.*;
import othello.model.ai.ComputerPlayer;
import othello.model.ai.EasyStrategy;
import othello.model.ai.HardStrategy;
import othello.model.game.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertTrue;

// maybe can be done better

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

@Disabled
public class ComputerPlayerTest {
    ComputerPlayer hardComputer;
   ComputerPlayer easyComputer;

   OthelloGame game;


    /**
     * sets up a new game with an "Easy Mode" player and a "Hard Mode" one
     */
    @BeforeEach
    public void setUp() {
        hardComputer = new ComputerPlayer(Mark.BLACK, new HardStrategy());
        easyComputer = new ComputerPlayer(Mark.WHITE, new EasyStrategy());
        game = new OthelloGame(hardComputer,easyComputer);
    }


    /**
     * tests if the game modes return their respective name correctly
     */
    @Test
    public void testName() {
        assertEquals("Hard Mode", hardComputer.getName());
        assertEquals("Easy Mode", easyComputer.getName());

    }

    /**
     * tests if the assignment/getMark function of marks works correctly
     */
    @Test
    public void testMark() {
        assertEquals(Mark.BLACK, hardComputer.getMark());
        assertEquals(Mark.WHITE, easyComputer.getMark());
    }

    /**
     * tests if the moves made by each of the modes are valid
     */
    @Test
    public void testIsDoingValidMoves() {

      assertTrue(game.isValidMove(hardComputer.determineMove(game)));
      assertTrue(game.isValidMove(easyComputer.determineMove(game)));


    }
}
