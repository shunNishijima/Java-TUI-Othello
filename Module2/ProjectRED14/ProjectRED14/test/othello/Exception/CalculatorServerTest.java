package othello.Exception;


class CalculatorServerTest {
    /**
    private static CalculatorFactory factory;

    @BeforeAll
    static void setup() {
        // static because a @BeforeAll must be a static method
        // therefore the field "factory" is also static

        factory = null; // FIXME replace with the actual factory
    }

    /**
     * Simple test using the CalculatorServer
     * @throws IOException
     *
    @Test
    void testBasics() throws IOException {
        var server = factory.makeCalculatorServer();

        // start a server on some available port. This is important, if we set a specific port, then this test will
        // fail if that specific port is not available
        int before = Thread.activeCount();
        server.start(0);
        int after = Thread.activeCount();
        assertTrue(after > before);

        // now ask the server what port it is listening on
        // this should be the actual port that the ServerSocket is listening to (see ServerSocket.getLocalPort)
        int port = server.getPort();
        assertTrue(port >= 1 && port <= 65535);

        server.stop();

        assertEquals(before, Thread.activeCount());
    }

    /**
     * Simple test using the CalculatorServer
     * @throws IOException
     *
    @Test
    void testNetworked() throws IOException {
        var server = factory.makeCalculatorServer();

        // start a server on some available port. This is important, if we set a specific port, then this test will
        // fail if that specific port is not available
        server.start(0);

        // now ask the server what port it is listening on
        // this should be the actual port that the ServerSocket is listening to (see ServerSocket.getLocalPort)
        int port = server.getPort();
        assertTrue(port >= 1 && port <= 65535);

        // if this fails, then typically the server is not accepting connections from the server socket
        // maybe the server thread is not running?
        var sock = new Socket(InetAddress.getLocalHost(), port);

        // a try-with-resources block to wrap the socket's streams in reader/writer -> bufferedreader/printwriter
        // we set autoflush to true for the printwriter, so println, printf will flush the output (= actually send it)
        try (var br = new BufferedReader(new InputStreamReader(sock.getInputStream()));
             var pw = new PrintWriter(new OutputStreamWriter(sock.getOutputStream()), true)) {
            pw.println("push 0000003");
            pw.println("push -123.00");
            pw.println("add");
            pw.println("pop");
            // at this point, the server should write the result of add (3, -123) so we should be able to read that
            assertEquals("-120.0", br.readLine());

            pw.println("push 40");
            pw.println("push 5.5");
            pw.println("sub");
            pw.println("pop");
            assertEquals("34.5", br.readLine());

            pw.println("push 100");
            pw.println("push 4");
            pw.println("mult");
            pw.println("pop");
            assertEquals("400.0", br.readLine());

            pw.println("push 10");
            pw.println("push 400");
            pw.println("div");
            pw.println("pop");
            assertEquals("0.025", br.readLine());
        }

        // this test does NOT test whether there are crashes in the server...
        // there are workarounds to accomplish this, for example the AsynchTester answer in
        // https://stackoverflow.com/questions/2596493/junit-assert-in-thread-throws-exception
        // however, we already have a StreamCalculatorTest which reads from a file and can handle reading errors

        // furthermore, this test does not check if multiple different clients can connect and use the calculator

        sock.close();
        server.stop();
    }*/
}
