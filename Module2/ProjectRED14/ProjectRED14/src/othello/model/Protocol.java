package othello.model;

/**
 * Protocol class with constants and methods for creating protocol messages
 */
public final class Protocol {
    private Protocol() {}
    public static final String SEPARATOR = "~";

    /**
     * Build a new protocol message which instructs a client that another client said something
     * @param from The name of the client that sent the message
     * @param command The message that was received from the client
     * @return the protocol message
     */
    public static String forwardMessage(String from, String command) {
        return command+SEPARATOR+from;
    }
}