package othello.model.server;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class ImplOthelloServer implements OthelloServer{
    private ServerSocket serverSocket;
    private Thread thread;
    private int port;
    private static List<OthelloClientHandler> clients = new ArrayList<>();
    private static boolean bool = false;

    /**
     * Starts the server. The server should run in a separate thread, so this method should return after starting this
     * thread. The server port depends on the implementation, for example, the port can be given in the constructor.
     * This method may only be run once.
     */
    /*@
        requires !isAccepting();
        ensures isAccepting();
    */
    @Override
    public void start() {
        try{
            serverSocket = new ServerSocket(port);
            thread = new Thread(this);
            thread.start();
            bool = true;
        }catch (IOException e){
            System.out.println("this port is used");
            e.printStackTrace();
        }
    }

    /**
     * Returns the port of the server. This method returns the actual port the server is accepting connections on.
     *
     * @return the port number, between 0 and 65535.
     */
    /*@
        ensures isAccepting() ==> \result>=0&&\result<=65535;
        pure;
    */
    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }

    /**
     * Stops the server. This method returns after the server thread has actually stopped.
     * This method may only be run once and only after start() has been called before.
     */
    /*@
        requires isAccepting();
        ensures !isAccepting();
    */
    @Override
    public void stop() {
        try{
            serverSocket.close();
            thread.join();
            bool = false;
        }catch (IOException|InterruptedException e){
            System.out.println("serverSocket must start before it");
            System.out.println("Or thread can not join");
            e.printStackTrace();
        }
    }

    /**
     * Returns true if the server is currently accepting connections, and false otherwise.
     */
    /*@
        pure;

    */
    @Override
    public boolean isAccepting() {
        return bool;
    }

    @Override
    public void handleOthelloCommand(OthelloClientHandler och, String command) {
        switch (command){
            case "LOGIN":
                for (OthelloClientHandler client: clients){
                    if(client.getUsername().equals(och.getUsername())){
                        command = "ALREADYLOGGEDIN";
                        break;
                    }
                }
                break;
            default:
                break;
        }
        for (OthelloClientHandler client: clients){
            client.sendCommand(och.getUsername(), command);
        }
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        try{
            while (!serverSocket.isClosed()){
                Socket socket = serverSocket.accept();
                OthelloClientHandler och = new OthelloClientHandler(socket,this);
                clients.add(och);
                new Thread(och).start();
            }
        }catch (IOException e){
            System.out.println("serverSocket can not accept");
            e.printStackTrace();
        }
    }

    public void setPort(int port) {
        this.port = port;
    }
}
