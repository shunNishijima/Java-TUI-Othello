package ss.week7.chat;

/**
 * Protocol class with constants and methods for creating protocol messages
 */
public final class Protocol {
    private Protocol() {}
    
    public static final String SAY = "SAY";
    public static final String FROM = "FROM";
    public static final String SEPARATOR = "~";

    /**
     * Build a new protocol message which instructs the server that you want to say something
     * @param message The message you want to send
     * @return the protocol message
     */
    public static String printMessage(String message) {
        return SAY + SEPARATOR + message;
    }

    /**
     * Build a new protocol message which instructs a client that another client said something
     * @param from The name of the client that sent the message
     * @param message The message that was received from the client
     * @return the protocol message
     */
    public static String forwardMessage(String from, String message) {
        return FROM + SEPARATOR + from + SEPARATOR + message;
    }
}
