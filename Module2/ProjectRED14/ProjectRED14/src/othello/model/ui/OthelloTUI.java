package othello.model.ui;
import othello.model.ai.ComputerPlayer;
import othello.model.ai.EasyStrategy;
import othello.model.ai.HardStrategy;
import othello.model.game.AbstractPlayer;
import othello.model.game.Mark;
import othello.model.game.OthelloGame;
import othello.model.game.Player;
import java.util.Scanner;

/**
 * TUI for Othello game which is turn based and we can choose user input based player or AI player.
 */
public class OthelloTUI {
    private boolean playing = true;

    /**
     * This is the main method to start run method which works actually othello game.
     */
    public static void main(String[] args) {
        System.out.println("start");
        OthelloTUI othelloTUI = new OthelloTUI();
        othelloTUI.run();
    }

    /**
     * This is run, which works actual show and move of othello game.
     */
    public void run(){
        //start new game until user enter no.
        while (playing) {
            Scanner scanner = new Scanner(System.in);
            System.out.println("What is your name? BLACK: ");
            String name = scanner.nextLine();
            Player player1;
            switch (name) {
                case "-E":
                    player1 = new ComputerPlayer(Mark.BLACK, new EasyStrategy());
                    break;
                case "-H":
                    player1 = new ComputerPlayer(Mark.BLACK,new HardStrategy());
                    break;
                default:
                    player1 = new HumanPlayer(name);
                    break;
            }
            System.out.println("What is your name? WHITE: ");
            name = scanner.nextLine();
            Player player2;
            switch (name) {
                case "-E":
                    player2 = new ComputerPlayer(Mark.BLACK, new EasyStrategy());
                    break;
                case "-H":
                    player2 = new ComputerPlayer(Mark.BLACK,new HardStrategy());
                    break;
                default:
                    player2 = new HumanPlayer(name);
                    break;
            }
            //Make new game and board.
            OthelloGame othelloGame = new OthelloGame(player1, player2);

            //Play game until the game is over
            while (!othelloGame.isGameOver()) {
                System.out.println(othelloGame.board.toString());
                //player pass if there is no valid move
                if (othelloGame.getValidMoves().isEmpty()) {
                    System.out.println(((AbstractPlayer) othelloGame.getTurn()).getName() + " pass");
                    othelloGame.switchTurn();
                } else {
                    //make move by determine move method
                    othelloGame.doMove(othelloGame.getTurn().determineMove(othelloGame));
                    //if game is over at this point print winner
                    if (othelloGame.isGameOver()) {
                        System.out.println(othelloGame.board.toString());
                        System.out.println(othelloGame.getWinner() + " is the winner!");
                        System.out.println("Hoe many BLACK is  "+othelloGame.board.countPieces()[1]);
                        System.out.println("Hoe many WHITE is  "+othelloGame.board.countPieces()[0]);
                    } else {
                        othelloGame.switchTurn();
                    }
                }
            }
            System.out.println("Game is over!");

            //ask player if play again.
            System.out.println("Do you want to play again? put y or n");
            Scanner input = new Scanner(System.in);
            String again = input.nextLine();
            switch (again) {
                case "y":
                    playing = true;
                    break;
                case "n":
                    playing = false;
                    break;
                default:
                    playing = false;
                    System.out.println("input is not valid, automatically finish");
                    break;
            }
        }
    }
}
