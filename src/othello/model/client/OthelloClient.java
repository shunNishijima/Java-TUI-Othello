package othello.model.client;
import othello.model.ai.ComputerPlayer;
import othello.model.ai.EasyStrategy;
import othello.model.ai.HardStrategy;
import othello.model.ai.Strategy;
import othello.model.game.*;
import othello.model.server.Protocol;
import othello.model.ui.HumanPlayer;
import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import othello.model.Exception.*;

/**
 * This is the Client function of Othello. It starts running until the connection with the server is broken.
 * It sends Protocol messages to the server to manage the game and process outside the game at the client
 * and the server respectively. This class makes a connection using user input of IP address and a port number.
 * The client has the game after receiving a new game message from the server to work independently.
 */
public class OthelloClient implements Client{
    private Socket socket;
    private final List<OthelloListener> othelloListeners = new ArrayList<>();
    private PrintWriter writer;
    private String username = "";
    private boolean login = false;
    private boolean gameStart = false;
    private boolean gameOver = false;
    private boolean connected;
    private OthelloGame game;
    private boolean iAmPlayer1;
    private boolean isEasy;
    private boolean isHuman=true;
    private final Lock lock = new ReentrantLock();
    private final Condition condition = lock.newCondition();
    private boolean x = true;
    public OthelloClient(){
    }

    /**
     * Make new socket connectable,
     * make new thread for the Client.
     *
     * @param inetAddress is address of server is wanted to connect.
     * @param port        port number of server.
     */
    /*@
        requires inetAddress!=null;
        requires port>=0&&port<=65535;
    */
    @Override
    public void connect(InetAddress inetAddress, int port) {
        try{
            socket = new Socket(inetAddress,port);
            System.out.println("Socket is connected at: "+port);
            writer = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()));
            //Client thread is started here.
            new Thread(this).start();
            connected = true;
        }catch (IOException e){
            System.out.println(Protocol.forwardError("port or host is wrong"));
        }
    }

    /**
     * make socket close.
     */
    @Override
    public void close() {
        try{
            socket.close();
            this.connected = false;
        }catch (IOException e){
            System.out.println(Protocol.forwardError("Socket is not open yet"));
        }
    }

    /**
     * sending commands from user input to the server.
     * commands must follow protocol.
     * @param command input from user as command.
     */
    @Override
    public synchronized void sendCommand(String command) throws InterruptedException, InvalidInput, InvalidMove {
        //make lock to the block
        lock.lock();
        try {
            String[] s = command.split(" ");
            //send messages following protocol.
            switch (s[0]) {
                case "HELLO":
                    writer.println(Protocol.clientHello(command));
                    writer.flush();
                    break;
                case "LOGIN":
                    writer.println(Protocol.clientLOGIN(command, username));
                    writer.flush();
                    break;
                case "QUEUE":
                case "LIST":
                    writer.println(command);
                    writer.flush();
                    break;
                case "MOVE":
                    //MOVE N is required
                    if (s.length > 1) {
                        //if it's your turn
                        if (game!=null&&(!gameOver&&((AbstractPlayer) game.getTurn()).getName().equals(username))) {
                            //Check if computer
                            if (game.getTurn() instanceof ComputerPlayer) {
                                //using determine move to create move.
                                //if there are no valid move, then pass
                                if (!game.getValidMoves().isEmpty()) {
                                    s[1] = "" + ((OthelloMove) game.getTurn().determineMove(game)).getLocation();
                                } else {
                                    System.out.println("pass");
                                    s[1] = "" + 64;
                                }
                                //if it's human, MOVE pass will be changed as MOVE 64
                            } else {
                                if (s[1].equals("pass")) {
                                    s[1] = "" + 64;
                                    //if MOVE SOMETHING is in valid input.
                                }
                            }
                            //if it's not your turn we don't send message
                        } else {
                            break;
                        }
                        //If there is no number after move, we don't send.
                    } else {
                        throw new InvalidMove();
                    }
                    //Before sending check if is valid move.
                    if(game.isValidMove(new OthelloMove(((AbstractPlayer) game.getTurn()).getMark(),Integer.parseInt(s[1]))) || s[1].equals("64") ){
                    System.out.println("OUTGOING "+Protocol.networkMOVE(s[0], s[1]));
                    writer.println(Protocol.networkMOVE(s[0], s[1]));
                    writer.flush();
                    } else {
                        throw new InvalidMove();
                    }
                    break;
                default:
                    x = false;
                    lock.unlock();
                    throw new InvalidInput();
            }
            if (x){condition.await();}
        }finally {if (x) {lock.unlock();}}
        x = true;
    }


    /**
     * used as add new listener for showing message from server.
     */
    @Override
    public void addOthelloListener(OthelloListener othelloListener) {
        othelloListeners.add(othelloListener);
    }

    /**
     * used check if login was successful.
     * @return if login was successful.
     */
    public boolean isLogin(){return this.login;}

    /**
     * used check if game is starting
     * @return game is starting or not.
     */
    public boolean isGameStart(){return this.gameStart;}

    /**
     * setter for gameStart
     * @param gameStart false if player is chosen
     */
    public void setGameStart(boolean gameStart) {this.gameStart = gameStart;}

    /**
     * Check if game is over
     * @return status of game
     */
    public boolean isGameOver() {return gameOver;}

    /**
     * run method for Thread of Client.
     */
    @Override
    public void run() {
        try{
            BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            String line;
            String[] splits;
            while ((line=br.readLine())!=null){
                splits = line.split("~");
                lock.lock();
                try {
                    switch (splits[0]) {
                        case "LOGIN"://LOGIN~username
                            login = true;
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived("Login has successful as " + username, username);
                            }
                            break;
                        case "NEWGAME"://NEWGAME~NAME1~NAME2
                            if (splits.length == 3) {
                                gameStart = true;
                                //Make new game according to NEWGAME from the server.
                                this.game = new OthelloGame(new HumanPlayer(splits[1], Mark.BLACK), new HumanPlayer(splits[2], Mark.WHITE));
                                this.iAmPlayer1 = splits[1].equals(this.username);
                                for (OthelloListener listener : othelloListeners) {
                                    listener.commandReceived("New Game has started with " + splits[1] + " and " + splits[2], username);
                                }
                            }
                            break;
                        case "GAMEOVER"://GAMEOVER~VICTORY~NAME
                            gameOver = true;
                            this.game = null;
                            //GAMEOVER VICTORY or DISCONNECT
                            if (splits.length > 2) {
                                for (OthelloListener listener : othelloListeners) {
                                    listener.commandReceived("Game is over " + "because " + splits[1] + " by " + splits[2], username);
                                }
                                //GAMEOVER DRAW
                            } else {
                                for (OthelloListener listener : othelloListeners) {
                                    listener.commandReceived("Game is over " + "because " + splits[1], username);
                                }
                            }
                            break;
                        case "HELLO"://HELLO~something
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived("HELLO!! " + splits[1], username);
                            }
                            break;
                        case "ALREADYLOGGEDIN":
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived("this name is already used. Can you change?", username);
                            }
                            break;
                        case "LIST"://LIST~A~B
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived("The list of user is below\n" + line, username);
                            }
                            break;
                        case "MOVE"://MOVE~N
                            if (splits.length == 2) {
                                //if it's game over, this message is mistake.
                                if (gameOver){
                                    break;
                                }
                                //receive pass command.
                                if (splits[1].equals("64")) {
                                    game.switchTurn();
                                    for (OthelloListener listener : othelloListeners) {
                                        listener.commandReceived("INCOMING "+line, username);
                                    }
                                    break;
                                }
                                //make new move according to the move command from the server,
                                Move move;
                                move = new OthelloMove(((AbstractPlayer) game.getTurn()).getMark(), Integer.parseInt(splits[1]));
                                //check if valid move.
                                if (game != null && game.isValidMove(move)) {
                                    game.doMove(move);
                                    game.switchTurn();
                                    System.out.println(game.board.toString());
                                } else {
                                    System.out.println(Protocol.forwardError("Invalid Move From Server"));
                                    break;
                                }
                            } else {
                                System.out.println(Protocol.forwardError("Malformed Move Command"));
                                break;
                            }
                            //successfully move executed.
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived("INCOMING "+line, username);
                            }
                            break;
                        case "ERROR":
                            System.out.println("heehxd");
                            if(splits.length>1){
                                String[] splitError = splits[1].split(" ");
                                if (Objects.equals(splitError[0], "MOVE")) {
                                    for (OthelloListener listener : othelloListeners) {
                                        listener.commandReceived(line, username);
                                    }
                                    this.setGameOver(true);
                                    this.close();
                                    break;
                                }
                            }
                            break;
                        default:
                            for (OthelloListener listener : othelloListeners) {
                                listener.commandReceived(line, username);
                            }
                            break;
                    }
                    //every thread awake.
                    condition.signal();
                }finally {lock.unlock();}
            }
        }catch (IOException e){
            System.out.println(Protocol.forwardError("No Connection, Press Enter to Exit"));
            this.close();
        }
    }

    /**
     * getting status of connection.
     * @return if connection is fine or not.
     */
    public boolean getConnection(){return this.connected;}

    /**
     * setter for username.
     * @param username set username for client.
     */
    public void setUsername(String username) {this.username = username;}

    /**
     * checker if it's human or computer.
     * @param human if it's human, true.
     */
    public void setHuman(boolean human) {isHuman = human;}

    /**
     * checker which strategy has been chosen.
     * @param easy if user select easy strategy, true.
     */
    public void setEasy(boolean easy) {isEasy = easy;}

    /**
     * set player for each client regarding user input.
     */
    public void setPlayer(){
        if (!isHuman){
            if (iAmPlayer1){
                if (isEasy){
                    game.setPlayer1(new ComputerPlayer( Mark.BLACK,new EasyStrategy(),username));
                    System.out.println("Player1 set! as easy AI");
                }else {
                    game.setPlayer1(new ComputerPlayer( Mark.BLACK,new HardStrategy(),username));
                    System.out.println("Player1 set! as hard AI");
                }
            }else {
                if (isEasy){
                    game.setPlayer2(new ComputerPlayer( Mark.WHITE,new EasyStrategy(),username));
                    System.out.println("Player2 set! as easy AI");
                }else {
                    game.setPlayer2(new ComputerPlayer( Mark.WHITE,new HardStrategy(),username));
                    System.out.println("Player2 set! as hard AI");
                }
            }
        }
    }

    /**
     * send back every valid moves for human player.
     * @return sequence of string represents valid moves.
     */
    public String giveHint(){
        if (((AbstractPlayer)game.getTurn()).getName().equals(username)){
            StringBuilder hint = new StringBuilder("Hint: ");
            for (Move move: game.getValidMoves()){
                hint.append(((OthelloMove) move).getLocation()).append(" ");
            }
            return hint.toString();
        }
        return null;
    }
    /**
     * send back every valid moves for human player.
     * @return sequence of string represents valid moves.
     */
    public String giveAI(){
        if (((AbstractPlayer)game.getTurn()).getName().equals(username)){
            Strategy AI = new HardStrategy();
            Move move = AI.determineMove(game);
            return "AI determine move as: "+((OthelloMove)move).getLocation();
        }
        return null;
    }

    /**
     * Check if game is over.
     * @param gameOver if game is over, true.
     */
    public void setGameOver(boolean gameOver) {this.gameOver = gameOver;}

    /**
     * Check if client is human.
     * @return if client is human player, true.
     */
    public boolean isHuman() {return isHuman;}
}
