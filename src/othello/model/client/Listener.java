package othello.model.client;

/**
 * As interface of Listener, provides common method as listener.
 * That is sending messages to all clients which they have listeners.
 */
public interface Listener {
    void commandReceived(String command, String username);
}
