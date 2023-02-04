package othello.model.client;
import othello.model.Exception.InvalidInput;
import othello.model.Exception.InvalidMove;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;
import java.util.concurrent.TimeUnit;

/**
 * Works as user interface of OthelloClient.
 * It allows user input for making connections with the server and all input during the game and outside the game.
 * Ask port number and IP address to connect to a socket. Also send Queue to the server for a new game.
 */
public class Othello {
    /**
     * As User interface of Client asks user input.
     * @throws InterruptedException for send command method.
     */
    public static void main(String[] args) throws InterruptedException, InvalidInput, InvalidMove {
        //ask address
        Scanner scanner = new Scanner(System.in);
        System.out.println("What is your address?");
        String address = scanner.nextLine();

        //ask port number until is valid
        Scanner input = new Scanner(System.in);
        System.out.println("What is your port number?");
        int port = input.nextInt();
        while (true){
            if(!(port>=0&&port<=65535)){
                System.out.println("Invalid. Enter port number again?");
                port = input.nextInt();
            }else {
                break;
            }
        }

        //make client and listener, connecting the socket.
        OthelloClient othelloClient = new OthelloClient();
        OthelloListener othelloListener = new OthelloListener();
        othelloClient.addOthelloListener(othelloListener);
        try{
            othelloClient.connect(InetAddress.getByName(address),port);
        }catch (UnknownHostException e){
            System.out.println("that address is invalid");
        }

        //Handshake is started
        //Command HELLO
        othelloClient.sendCommand("HELLO");//HELLO~Server
        try {
            TimeUnit.SECONDS.sleep(1);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        System.out.println("What is your name?");
        String username = scanner.nextLine();
        othelloClient.setUsername(username);

        //command LOGIN
        othelloClient.sendCommand("LOGIN");//LOGIN
        try {
            TimeUnit.SECONDS.sleep(1);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        while(!othelloClient.isLogin()){
            System.out.println("Enter other name: ");
            username = scanner.nextLine();
            othelloClient.setUsername(username);
            othelloClient.sendCommand("LOGIN");
            try {
                TimeUnit.SECONDS.sleep(1);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        othelloClient.sendCommand("QUEUE");
        //Handshake is finished.

        boolean playing = false;
        //loop while connected to socket
        while (othelloClient.getConnection()) {
            //until game has not started yet do nothing.
            while (!playing){
                if (othelloClient.isGameStart()){
                    System.out.println("Play as Human(1) or Computer(2)?");
                    String human = scanner.nextLine();
                    othelloClient.setHuman(human.equals("1"));
                    if (!human.equals("1")){
                        System.out.println("Play as Easy(1) or Hard(2)?");
                        String easy = scanner.nextLine();
                        othelloClient.setEasy(easy.equals("1"));
                    }
                    othelloClient.setPlayer();
                    othelloClient.setGameStart(false);
                    playing = true;
                    break;
                }
            }

            //game is over, directly go to the QUEUE.
            if (othelloClient.isGameOver()){
                playing = false;
                othelloClient.sendCommand("QUEUE");
                othelloClient.setGameOver(false);
            }

            //game is still doing, if computer send MOVE 100 infinitely
            if (playing) {
                if (!othelloClient.isHuman()) {
                    othelloClient.sendCommand("MOVE 100");
                } else {
                    System.out.println("Command(LIST,MOVE index,HINT,HELP,AI)");
                    String command = scanner.nextLine();
                    switch (command) {
                        case "HELP":
                            System.out.println(
                                    " This is the Command List\n" +
                                            " * LIST: show every client name is connected in server\n" +
                                            " * MOVE: during the game 'MOVE number' means put mark to the number. Use move pass if you don't have valid moves\n" +
                                            " * HINT: during the game \n" +
                                            " * HELP: show help menu");
                            break;
                        case "HINT":
                            System.out.println(othelloClient.giveHint());
                            break;
                        case "AI":
                            System.out.println(othelloClient.giveAI());
                            break;
                        default:
                            othelloClient.sendCommand(command);
                            break;
                    }
                }
            }
        }
        System.out.println("Thank You for Playing!");
    }
}