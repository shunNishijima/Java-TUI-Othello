package othello.model.server;

import java.util.Scanner;

public class OthelloServerApplication {
    public static void main(String[] args) {
        //need port number until it success to use.
        Scanner input = new Scanner(System.in);
        ImplOthelloServer server = new ImplOthelloServer();
        while (!server.isAccepting()){
            System.out.println("Port number?");
            int port = input.nextInt();
            server.setPort(port);
            server.start();
            System.out.println("port number is: "+server.getPort());
        }


        Scanner scanner = new Scanner(System.in);
        System.out.println("Command...  ");
        boolean bool = true;
        while (bool){
            String line;
            switch (line=scanner.nextLine()){
                case "LIST":
                    //'LIST~Charlie~Alice~Bob'
                case "NEWGAME":
                    //'NEWGAME~Alice~Bob'
                case "MOVE":
                    //'MOVE~15'
                case "GAMEOVER":
                    //For a game won by Alice: 'GAMEOVER~VICTORY~Alice'
                default:
            }
        }
    }
}
