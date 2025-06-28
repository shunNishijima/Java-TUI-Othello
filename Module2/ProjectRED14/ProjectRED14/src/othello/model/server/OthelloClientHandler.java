package othello.model.server;

import othello.model.Protocol;
import othello.model.game.Game;
import othello.model.game.Move;
import othello.model.game.OthelloMove;
import othello.model.game.Player;

import java.io.*;
import java.net.Socket;

public class OthelloClientHandler implements  Runnable{
    private Socket socket;
    private OthelloServer othelloServer;
    private String username;

    public OthelloClientHandler(Socket socket,OthelloServer othelloServer){
        this.othelloServer = othelloServer;
        this.socket =socket;
    }
    /**
     * When an object implementing interface <code>Runnable</code> is used
     * to create a thread, starting the thread causes the object's
     * <code>run</code> method to be called in that separately executing
     * thread.
     * <p>
     * The general contract of the method <code>run</code> is that it may
     * take any action whatsoever.
     *
     * @see Thread#run()
     */
    @Override
    public void run() {
        try{
            BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            String line = br.readLine();
            username = line;
            while ((line = br.readLine())!=null){
                othelloServer.handleOthelloCommand(this,line);
            }
            br.close();
        }catch (IOException e){
            System.out.println("input is invalid");
            close();
            othelloServer.stop();
            e.printStackTrace();
        }
    }
    public void sendCommand(String username,String command){
        try{
            PrintWriter pw = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()));
            switch (command){
                case "ALREADYLOGGEDIN":
                    pw.println(command);
                    pw.flush();
                    break;
                default:
                    pw.println(Protocol.forwardMessage(username,command));
                    pw.flush();
            }
        }catch (IOException e){
            System.out.println("Nothing in Server");
            close();
            e.printStackTrace();
        }
    }
    public void close(){
        try{
            socket.close();
        }catch (IOException e){
            System.out.println("Socket is not open yet");
            e.printStackTrace();
        }
    }

    public String getUsername() {
        return username;
    }
}
