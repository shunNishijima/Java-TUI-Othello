package othello.model.client;

/**
 * According to the listener model,
 * this is working as a listener which sends and shows messages from server instead of clients.
 * It provides us flexibility in terms of implementation.
 */
public class OthelloListener implements Listener{
    /**
     * this method shows messages from server at all clients interface.
     * @param command exactly output from Client
     * @param username for checking where this message came from
     */
    @Override
    public void commandReceived(String command, String username) {
        System.out.println(command);
    }
}
