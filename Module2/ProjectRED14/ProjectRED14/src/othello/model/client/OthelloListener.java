package othello.model.client;

import othello.model.Protocol;
import othello.model.game.OthelloMove;
import othello.model.game.Player;

public class OthelloListener implements Listener{
    /**
     * @param command
     * @param username
     */
    @Override
    public void commandReceived(String command, String username) {
        System.out.println(command);
    }
}
