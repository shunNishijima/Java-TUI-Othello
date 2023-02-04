package othello.model.client;
import othello.model.Exception.InvalidInput;
import othello.model.Exception.InvalidMove;
import java.net.InetAddress;

/**
 * As an interface of Client, it provides common commands for working as a client in networking development.
 */
public interface Client extends Runnable{
    void connect(InetAddress inetAddress, int port);
    void close();
    void sendCommand(String command) throws InterruptedException, InvalidInput, InvalidMove;
    void addOthelloListener(OthelloListener othelloListener);
}
