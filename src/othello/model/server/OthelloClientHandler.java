package othello.model.server;
import othello.model.game.OthelloGame;
import java.io.*;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * It is created by the server to communicate with clients respectively.
 * Receive messages from client and send to the server and also send commands from the server to clients.
 */
public class OthelloClientHandler implements  Runnable{
    private final Socket socket;
    private final OthelloServer othelloServer;
    private String username = "Instant";
    private OthelloGame game;
    private PrintWriter pw;
    private final Lock lock = new ReentrantLock();
    private final Condition condition = lock.newCondition();
    private boolean receiveMove=true;
    private boolean locked;



    /**
     * Constructor of ClientHandler.
     * @param socket socket which server is using.
     * @param othelloServer exact server which this client handler communicate.
     */
    public OthelloClientHandler(Socket socket,OthelloServer othelloServer){
        this.othelloServer = othelloServer;
        this.socket =socket;
    }
    /**
     * run for this thread.
     */
    @Override
    public void run() {
            try {
                pw = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()));
                BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                String line;
                String[] splits;
                while ((line = br.readLine()) != null) {
                    splits = line.split("~");
                    switch (splits[0]) {
                        case "MOVE":
                            lock.lock();
                            locked = true;
                            while (!receiveMove){
                            condition.await();}
                            receiveMove=false;
                            othelloServer.handleOthelloCommand(this, line);
                            break;
                        case "LOGIN":
                            this.username = splits[1];
                        case "HELLO":
                        case "LIST":
                        case "QUEUE":
                            othelloServer.handleOthelloCommand(this, line);
                            break;
                        default:
                            othelloServer.handleOthelloCommand(this, "Input is Invalid");
                            break;
                    }
                }
                br.close();
            } catch (IOException | InterruptedException e) {
                System.out.println(Protocol.forwardError("input was not reached"));//Clients disconnected
                try {
                    othelloServer.handleOthelloCommand(this, "DISCONNECT");
                } catch (IOException | InterruptedException ex) {
                    System.out.println("can not send");
                }
            }
    }

    /**
     * Sending command to Client.
     * @param username username of this client.
     * @param command command from server.
     */
    public void sendCommand(String username,String command){
            String[] splits = command.split("~");
            switch (splits[0]) {
                case "MOVE":
                    pw.println(command);//COMMAND~A~B
                    pw.flush();
                    if (locked){
                    condition.signal();
                    lock.unlock();
                    locked=false;}
                    receiveMove=true;
                    break;
                case "HELLO":
                case "ALREADYLOGGEDIN":
                case "LOGIN":
                case "LIST":
                case "NEWGAME":
                    System.out.println(command);
                case "GAMEOVER":
                    pw.println(command);//COMMAND~A~B
                    pw.flush();
                    break;
                default:
                    pw.println(Protocol.forwardError(command));
                    pw.flush();
                    break;
        }
    }

    /**
     * make socket close.
     */
    public void close(){
        try{
            socket.close();
        }catch (IOException e){
            System.out.println(Protocol.forwardError("Socket Is Not Open Yet"));
            e.printStackTrace();
        }
    }

    /**
     * return username
     * @return username of client.
     */
    public String getUsername() {
        return this.username;
    }

    /**
     *
     * @param l list of Client handler.
     * @return list of string name of client handlers.
     */
    public List<String> getList(List<OthelloClientHandler> l)  {
        List<String> list= new ArrayList<>();
        int i = 0;
        while (i<l.size()){
            System.out.println();
            list.add(l.get(i).getUsername());
            i++;
        }
        return list;
    }

    /**
     * This is the setter for username
     * @param username is username will be put on this client handler
     */
    public void setUsername(String username){
        this.username = username;
    }

    /**
     * this is getter for the game this client handler joined.
     * @return Object of game.
     */
    public OthelloGame getGame() {
        return game;
    }

    /**
     * setter for the game. The game is created by the server with this client handler, add.
     * @param game game which this client plays
     */
    public void setGame(OthelloGame game) {
        this.game = game;
    }
}

