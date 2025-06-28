package othello.model.client;

import othello.model.game.OthelloMove;
import othello.model.game.Player;

public interface Listener {
    void commandReceived(String command, String username);
}
