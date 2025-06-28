package ss.week7.chat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import ss.week7.chat.server.ChatServer;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

@Disabled
public class ServerTest {

    private ChatServer server;

    @BeforeEach
    void setUp() throws IOException {
         // FIXME use your own server implementation here
         // server = new ....
    }

    @Test
    void testChat() throws IOException {
        assertFalse(server.isAccepting());

        // start the server
        server.start();

        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);

        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());  // connect to the server
        String s;

        // using a try-with-resources block, we ensure that reader/writer are closed afterwards
        try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true)) {

            // Write our name (MyName)
            printWriter.println("MyName");

            // Write a bunch of messages, that are incorrect. Server should ignore them and not crash.
            printWriter.println("Hey!");
            printWriter.println("Hello?");
            printWriter.println("Oh yeah!");

            // Send a valid message now
            printWriter.println("SAY~Hey!");

            // We should get back the valid message that we sent
            s = bufferedReader.readLine();
            assertEquals("FROM~MyName~Hey!", s);

            // Test it one more time
            printWriter.println("SAY~Hello Again!");
            s = bufferedReader.readLine();
            assertEquals("FROM~MyName~Hello Again!", s);

            // Close the connection.
            socket.close();
        } finally {
            // Stop the server.
            server.stop();
            assertFalse(server.isAccepting());
        }
    }
}
