package othello.model.client;

import othello.model.game.Player;

import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

public class Othello {
    public static void main(String[] args) {
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
                System.out.println("this number is invalid.");
                System.out.println("What is your port number again?");
                port = input.nextInt();
            }else {
                break;
            }
        }

        //ask username which may be -E,-H
        System.out.println("What is your name?");
        String username = scanner.nextLine();

        OthelloClient othelloClient = new OthelloClient();
        OthelloListener othelloListener = new OthelloListener();
        othelloClient.addOthelloListener(othelloListener);

        try{
            othelloClient.connect(InetAddress.getByName(address),port);
            //send username to Client
            othelloClient.sendUsername(username);
            othelloClient.sendCommand("LOGIN");
            //if it's not sucessed we have to ask username again.

            othelloClient.sendCommand("HELLO");
        }catch (UnknownHostException e){
            System.out.println("that address is invalid");
            e.printStackTrace();
        }

        //get Command from user input especially about move.
        while (true){
            System.out.println("Command...");
            String command = scanner.nextLine();
            if(command!=null){
                othelloClient.sendCommand(command);
            }
        }
    }
}
