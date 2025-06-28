package othello.model.client;

import othello.model.Protocol;
import othello.model.game.OthelloMove;
import othello.model.game.Player;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class OthelloClient implements Client{
    private Socket socket;
    private List<OthelloListener> othelloListeners = new ArrayList<>();
    private PrintWriter writer;
    private String username;
    /**
     * @param inetAddress
     * @param port
     * @return
     */
    @Override
    public boolean connect(InetAddress inetAddress, int port) {
        try{
            socket = new Socket(inetAddress,port);
            System.out.println("the port now connected is: "+port);
            writer = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()));
            new Thread(this).start();
            return true;
        }catch (IOException e){
            System.out.println("port or host is wrong");
            e.printStackTrace();
            return false;
        }
    }

    /**
     *
     */
    @Override
    public void close() {
        try{
            socket.close();
        }catch (IOException e){
            System.out.println("Socket is not open yet");
            e.printStackTrace();
        }
    }

    /**
     * @param username
     * @return
     */
    @Override
    public boolean sendUsername(String username) {
        this.username = username;
        writer.println(username);
        writer.flush();
        return true;
    }

    /**
     * @param command
     * @return
     */
    @Override
    public boolean sendCommand(String command) {
        writer.println(command);
        writer.flush();
        return true;
    }

    /**
     *
     */
    @Override
    public void addOthelloListener(OthelloListener othelloListener) {
        othelloListeners.add(othelloListener);
    }

    /**
     *
     */
    @Override
    public void removeOthelloListener(OthelloListener othelloListener) {
        othelloListeners.remove(othelloListener);
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
            String line;
            while ((line=br.readLine())!=null){
                switch (line){
                    case "ALREADYLOGGEDIN":
                        System.out.println("new name?");
                        username = new Scanner(System.in).nextLine();
                }
                for(OthelloListener listener : othelloListeners){
                    listener.commandReceived(line,username);
                }
            }
        }catch (IOException e){
            System.out.println("input is invalid");
            e.printStackTrace();
        }
    }
}
