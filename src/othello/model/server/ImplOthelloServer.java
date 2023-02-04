package othello.model.server;
import othello.model.game.*;
import othello.model.ui.NetworkPlayer;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

/**
 * It provides the server function for a Othello game with network connection.
 * Make a server socket by a port number as input from the user.
 * Will be connected by several clients and communicate with them.
 */

public class ImplOthelloServer implements OthelloServer {
    private ServerSocket serverSocket;
    private Thread thread;
    private int port;
    private static final List<OthelloClientHandler> clients = new ArrayList<>();
    private static final Queue<OthelloClientHandler> queues = new LinkedList<>();
    private static final List<OthelloGame> games = new ArrayList<>();
    private boolean bool = false;
    public PipedWriter pipeWriter = new PipedWriter();
    public PipedReader pipedReader = new PipedReader();

    /**
     * Starts the server. The server should run in a separate thread, so this method should return after starting this
     * thread. The server port depends on the implementation, for example, the port can be given in the constructor.
     * This method may only be run once.
     * make new Server Socket
     * make new Thread of Server
     * start run()
     */
    /*@
        requires !isAccepting();
        ensures isAccepting();
    */
    @Override
    public void start() {
        try {
            serverSocket = new ServerSocket(port);
            System.out.println("Start server at: " + serverSocket.getLocalPort());
            thread = new Thread(this);
            thread.start();
            bool = true;
            pipedReader.connect(pipeWriter);
        } catch (IOException e) {
            System.out.println("this port is used");
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
        try {
            serverSocket.close();
            thread.join();
            bool = false;
        } catch (IOException | InterruptedException e) {
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

    /**
     * working make command from client through client handler to match Protocol and do some tasks
     *
     * @param och     client handler
     * @param command command from client.
     * @throws IOException if is invalid.
     */
    @Override
    public synchronized void handleOthelloCommand(OthelloClientHandler och, String command) throws IOException {
            String[] splits = command.split("~");
            //check if client is created.
            if (clients.size() > 0) {
                switch (splits[0]) {
                    case "HELLO":
                        System.out.println(command);//HELLO~Client
                        och.sendCommand(och.getUsername(), Protocol.serverHello(splits[0]));//HELLO~Server
                        break;
                    case "LOGIN":
                        System.out.println(command);//LOGIN~username
                        int count = 0;
                        for (OthelloClientHandler client : clients) {
                            if (client.getUsername().equals(och.getUsername())) {
                                count++;
                            }
                        }
                        if (count > 1) {//If same name is used before.
                            command = "ALREADYLOGGEDIN";
                        }
                        och.sendCommand(och.getUsername(), command);//LOGIN~username
                        break;
                    case "LIST":
                        System.out.println(command);//LIST
                        BufferedWriter bufferedWriter = new BufferedWriter(pipeWriter);
                        bufferedWriter.write(clients.size() + "\n");
                        for (OthelloClientHandler client : clients) {
                            bufferedWriter.write(client.getUsername());
                        }
                        bufferedWriter.flush();
                        och.sendCommand(och.getUsername(), Protocol.forwardList(och.getList(clients), command));//LIST~a~b
                        break;
                    case "QUEUE":
                        System.out.println(command);//QUEUE
                        if (queues.contains(och)) {//if queue command sent twice, remove.
                            queues.remove(och);
                            System.out.println("The size of Queue now is: " + queues.size());
                        } else {
                            queues.add(och);
                            System.out.println("The size of Queue now is: " + queues.size());
                        }
                        if (queues.size() > 1) {//start NEW GAME using 2 players in queues
                            OthelloClientHandler och1 = queues.poll();
                            OthelloClientHandler och2 = queues.poll();
                            Player player1 = new NetworkPlayer(Mark.BLACK, och1.getUsername());
                            assert och2 != null;
                            Player player2 = new NetworkPlayer(Mark.WHITE, och2.getUsername());
                            //make new game.
                            OthelloGame game = new OthelloGame(player1, player2);

                            //games is increased
                            games.add(game);
                            //set game to each client handler
                            och1.setGame(game);
                            och2.setGame(game);
                            System.out.println("Now the size of games is: " + games.size());
                            System.out.println(game.board.toString());

                            //send message to two clients
                            och1.sendCommand(och1.getUsername(), Protocol.serverNEWGAME(och1.getUsername(), och2.getUsername()));
                            och2.sendCommand(och2.getUsername(), Protocol.serverNEWGAME(och1.getUsername(), och2.getUsername()));
                        }
                        break;
                    case "MOVE":
                        //game is over or this is not your turn then do nothing
                        if (och.getGame()!=null&&(och.getGame().isGameOver() || !((AbstractPlayer) och.getGame().getTurn()).getName().equals(och.getUsername()))) {
                            for (OthelloClientHandler client : clients) {
                                //send back invalid move and break.
                                if (client.getGame().equals(och.getGame())) {
                                    client.sendCommand(och.getUsername(), command);
                                }
                            }
                            break;
                        }

                        //only player turn is now can play
                        if(splits.length>1){
                        int index = Integer.parseInt(splits[1]);
                        //if Move~64 is received, make a pass
                        if (index == 64) {
                            System.out.println("pass");
                            och.getGame().switchTurn();
                            System.out.println(((AbstractPlayer) och.getGame().getTurn()).getName());
                            //send back to clients
                            for (OthelloClientHandler client : clients) {
                                if (client.getGame() .equals( och.getGame())) {
                                    client.sendCommand(och.getUsername(), command);
                                }
                            }
                            break;
                        }

                        //make a move
                        ((NetworkPlayer) och.getGame().getTurn()).setLocation(index);
                        Move move = och.getGame().getTurn().determineMove(och.getGame());
                        //check if valid move
                        if (!och.getGame().isValidMove(move)) {
                            //if not, send back to client ERROR message.
                            och.sendCommand(och.getUsername(), Protocol.forwardError(command));
                            break;
                        }
                        //if is valid move, do move.
                        och.getGame().doMove(move);

                        System.out.println(command);//MOVE~N
                        System.out.println(och.getGame().board.toString());
                        och.getGame().switchTurn();

                        //send back the move.
                        for (OthelloClientHandler client : clients) {
                            if (client.getGame().equals(och.getGame())) {
                                client.sendCommand(och.getUsername(), command);
                            }
                        }}

                        //Check if game is over
                        if (och.getGame()!=null&&och.getGame().isGameOver()) {
                            System.out.println("How many BLACK is  " + och.getGame().board.countPieces(Mark.BLACK));
                            System.out.println("How many WHITE is  " + och.getGame().board.countPieces(Mark.WHITE));
                            if (och.getGame().getWinner() != null) {
                                for (OthelloClientHandler client : clients) {
                                    if (client.getGame() .equals(och.getGame())) {
                                        //GAMEOVER~VICTORY~NAME
                                        client.sendCommand(och.getUsername(), Protocol.serverGAMEOVERVICTORY(((NetworkPlayer) och.getGame().getWinner()).getName()));
                                    }
                                }
                                //DRAW case is below
                            } else {
                                for (OthelloClientHandler client : clients) {
                                    if (client.getGame().equals(och.getGame())) {
                                        client.sendCommand(och.getUsername(), Protocol.serverGAMEOVERDRAW());
                                    }
                                }
                            }
                            //Game is finished then delete the game.
                            games.remove(och.getGame());
                        }
                        break;
                    case "DISCONNECT":
                        //check if disconnect during playing the game
                        if (!games.contains(och.getGame())) {
                            System.out.println(och.getUsername()+" has disconnected.");
                            och.close();
                            clients.remove(och);
                            break;
                        }
                        //during the game.
                        for (OthelloClientHandler client : clients) {
                            if (client.getGame() .equals( och.getGame())) {
                                client.sendCommand(och.getUsername(), Protocol.serverGAMEOVERDISCONNECT(och.getUsername()));
                            }
                        }
                        games.remove(och.getGame());
                        och.close();
                        clients.remove(och);
                        break;
                    default:
                        System.out.println(Protocol.forwardError("Invalid Input"));
                        och.sendCommand(och.getUsername(), "Input is Invalid");
                        break;
                }
            } else {
                och.sendCommand("Instant", "client has not created");
        }
    }

    /**
     * Runs this operation.
     * make link to Socket
     * make new Client handler
     * make new thread for client handler and start.
     */
    @Override
    public void run() {
        synchronized (clients) {
            try {
                while (!serverSocket.isClosed()) {
                    Socket socket = serverSocket.accept();
                    System.out.println("Get connection to this socket: " + socket.getInetAddress().getHostAddress());
                    OthelloClientHandler och = new OthelloClientHandler(socket, this);
                    clients.add(och);
                    System.out.println("Client Handler created and size: " + clients.size());
                    new Thread(och).start();
                }
            } catch (IOException e) {
                System.out.println(Protocol.forwardError("Server Socket is not Accepting"));
            }
        }
    }

    /**
     * port is set.
     *
     * @param port port number.
     */
    public void setPort(int port) {
        this.port = port;
    }

    /**
     * return List of client handler now.
     *
     * @return current List of client handler.
     */
    public List<OthelloClientHandler> getClients() {
        return clients;
    }
}
