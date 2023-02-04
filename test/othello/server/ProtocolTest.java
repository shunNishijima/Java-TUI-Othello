package othello.server;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import othello.model.server.ImplOthelloServer;
import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

/**
 * The test of Protocol checks server sending protocol messages correctly
 * Our expectation are
 * When a command gets sent to the server in different order than intended
 * as the server shouldn’t crash but acknowledge the error and send appropriate message
 * When a message that doesn’t follow protocol gets sent to the server,
 * it shouldn’t crash but acknowledge the error and send appropriate message
 */
public class ProtocolTest {
    ImplOthelloServer server;

    Socket socket;

    /**
     * setting up default.
     * server start running and make a socket.
     * @throws IOException If input is invalid.
     */
    @BeforeEach
    public void setUp() throws IOException {
        server = new ImplOthelloServer();
        server.start();
        socket = new Socket(InetAddress.getLocalHost(), server.getPort());

    }

    /**
     * Checking if all Protocol messages are handled correctly.
     * @throws IOException if input was invalid.
     */
        @Test
        public void testNonProtocolInputToServer() throws IOException{
            try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                 PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true)) {

                printWriter.println("HELLO");


                printWriter.println("username");
                Assertions.assertEquals("HELLO~Server", bufferedReader.readLine());

                printWriter.println("MOVE");
                Assertions.assertEquals("ERROR~Input is Invalid", bufferedReader.readLine());

                printWriter.println("fwefewf");
                Assertions.assertEquals("ERROR~Input is Invalid", bufferedReader.readLine());

                printWriter.println("GAMEOVER");
                Assertions.assertEquals("ERROR~Input is Invalid", bufferedReader.readLine());
            }finally{
                System.out.println(":)");
            }
        }
}
