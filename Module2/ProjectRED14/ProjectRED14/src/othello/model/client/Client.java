package othello.model.client;

import othello.model.game.OthelloMove;
import othello.model.game.Player;

import java.net.InetAddress;

public interface Client extends Runnable{
    boolean connect(InetAddress inetAddress,int port);
    void close();
    boolean sendUsername(String username);
    boolean sendCommand(String command);
    void addOthelloListener(OthelloListener othelloListener);
    void removeOthelloListener(OthelloListener othelloListener);

}
