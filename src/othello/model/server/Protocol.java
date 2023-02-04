package othello.model.server;
import java.util.List;

/**
 * Provides a function which changes
 * command to Protocol type of messages which are sufficiently used for
 * communication between Clients and the server at the network.
 */
public final class Protocol {
    public static final String SEPARATOR = "~";

    /**
     * make changes in messages from clients as Protocol server should receive
     * @param command available command which client can use.
     * @return messages match Protocol
     */
    public static String clientHello(String command) {
        return command+SEPARATOR+"Client";
    }//HELLO~Client by Username
    /**
     * make changes in messages from server as Protocol clients should receive
     * @param command available command which server can use.
     * @return messages match Protocol
     */
    public static String serverHello(String command) {
        return command+SEPARATOR+"Server";
    }
    /**
     * make changes in messages from clients as Protocol server should receive
     * @param command available command which client can use.
     * @param username name of the client handler.
     * @return messages match Protocol
     */
    public static String clientLOGIN(String command,String username) {
        return command+SEPARATOR+username;
    }//LOGIN~Username
    /**
     * make changes in messages from server as Protocol clients should receive
     * @param p1 is one of the player for the new game
     * @param p2 is one of the player for the new game
     * @return messages match Protocol
     */
    public static String serverNEWGAME(String p1,String p2) {
        return "NEWGAME"+SEPARATOR+p1+SEPARATOR+p2;
    }
    /**
     * make changes in messages from server as Protocol clients should receive
     * @param username name of the client handler which is winner
     * @return messages match Protocol
     */
    public static String serverGAMEOVERVICTORY(String username) {
        return "GAMEOVER"+SEPARATOR+"VICTORY"+SEPARATOR+username;
    }
    /**
     * make changes in messages from server as Protocol clients should receive.
     * @return messages match Protocol
     */
    public static String serverGAMEOVERDRAW() {return "GAMEOVER"+SEPARATOR+"DRAW";}
    /**
     * make changes in messages from clients as Protocol server should receive
     * @param winner is the name of client handler who are still in connection.
     * @return messages match Protocol
     */
    public static String serverGAMEOVERDISCONNECT(String winner) {
        return "GAMEOVER"+SEPARATOR+"DISCONNECT"+SEPARATOR+winner;
    }
    /**
     * make changes in messages from clients as Protocol server should receive
     * also make changes in messages from server as Protocol clients should receive as well.
     * @param command available command which client can use.
     * @param index the string type of the index location of the board.
     * @return messages match Protocol
     */
    public static String networkMOVE(String command, String index) {
        return command+SEPARATOR+index;
    }//MOVE~index
    /**
     * make changes in messages from server as Protocol clients should receive
     * @param command available command which client can use.
     * @param list list of names of the client handlers.
     * @return messages match Protocol
     */
    public static String forwardList(List<String> list, String command){
        StringBuilder listString = new StringBuilder(command);
        for(String user: list){
            listString.append(SEPARATOR).append(user);
        }
        return listString.toString();
    }

    /**
     * Any errors in server should be notified to clients as sufficient as Protocol.
     * That's the same as client side.
     * It makes changes in error messages to be consumed as Protocol messages.
     * @param description reason of the errors
     * @return message matches Protocol
     */
    public static String forwardError(String description){
        return "ERROR~"+description;
    }
}