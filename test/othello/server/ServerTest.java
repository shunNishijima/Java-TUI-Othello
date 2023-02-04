package othello.server;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.model.server.ImplOthelloServer;
import othello.model.server.OthelloServer;
import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.concurrent.TimeUnit;

/**
 * Test server checks server works correctly.
 * The game Server should be able to connect and communicate with any client using the proper protocol.
 * The client should be able to request and send data to the server using predefined commands and
 * following the protocol. In the case of bad protocol the server should not crash.
 */
public class ServerTest {
    private OthelloServer server;

    /**
     * setting up new server.
     */
    @BeforeEach
    void setUp() {
         server = new ImplOthelloServer();
    }

    /**
     * Check all messages return from the server to the client follows Protocol.
     * @throws IOException if input was invalid.
     */
    @Test
    void testCommand() throws IOException {
        Assertions.assertFalse(server.isAccepting());

        // start the server
        server.start();

        Assertions.assertTrue(server.isAccepting());
        Assertions.assertTrue(server.getPort() > 0);
        Assertions.assertTrue(server.getPort() <= 65535);


        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());  // connect to the server
        try {
            TimeUnit.SECONDS.sleep(1);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        //ClientHandler is created.
        Assertions.assertTrue(((ImplOthelloServer)server).getClients().size()>0);
        String s;

        // using a try-with-resources block, we ensure that reader/writer are closed afterwards
        try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
             PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true)){

            // Send a valid message
            printWriter.println("HELLO~Client");
            // We should get back the valid message that we sent
            s = bufferedReader.readLine();
            Assertions.assertEquals("HELLO~Server", s);

            // Send a valid message now
            printWriter.println("LOGIN~Myname");
            // We should get back the valid message that we sent
            s = bufferedReader.readLine();
            System.out.println(s);
            Assertions.assertEquals("LOGIN~Myname", s);

            // Send a valid message
            printWriter.println("LIST");
            // We should get back the valid message that we sent
            s = bufferedReader.readLine();
            System.out.println(s);
            Assertions.assertEquals("LIST~Myname", s);

            // Send a valid message
            printWriter.println("QUEUE");

            // Close the connection.
            socket.close();
        } finally {
            // Stop the server.
            server.stop();
            Assertions.assertFalse(server.isAccepting());
        }
    }

}
