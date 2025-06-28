package ss.week7.chat.server;

/**
 * A chat server that runs in a separate thread.
 * The start method is only called once and the stop method is only called once after start.
 */
public interface ChatServer {
    /**
     * Starts the server. The server should run in a separate thread, so this method should return after starting this
     * thread. The server port depends on the implementation, for example, the port can be given in the constructor.
     * This method may only be run once.
     */
    //@ \requires !isAccepting();
    //@ \ensures isAccepting();
    void start();

    /**
     * Returns the port of the server. This method returns the actual port the server is accepting connections on.
     * @return the port number, between 0 and 65535.
     */
    //@ \ensures isAccepting() ==> \result > 0 && \result <= 65535;
    //@ pure;
    int getPort();

    /**
     * Stops the server. This method returns after the server thread has actually stopped.
     * This method may only be run once and only after start() has been called before.
     */
    //@ \requires isAccepting();
    //@ \ensures !isAccepting();
    void stop();

    /**
     * Returns true if the server is currently accepting connections, and false otherwise.
     */
    //@ pure;
    boolean isAccepting();
}
