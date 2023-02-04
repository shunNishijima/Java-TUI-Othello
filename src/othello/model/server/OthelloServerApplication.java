package othello.model.server;
import java.util.Scanner;
/**
 * This is User interface for OthelloServer.
 * It is needed to get input as a port number from the user.
 * Ask again until it gets the port number which has not been used yet.
 */
public class OthelloServerApplication {
    public static void main(String[] args) {
        //ask port number until it success to use.
        Scanner input = new Scanner(System.in);
        ImplOthelloServer server = new ImplOthelloServer();
        while (!server.isAccepting()){
            System.out.println("Port number?");
            int port = input.nextInt();
            server.setPort(port);
            server.start();
        }
    }
}
