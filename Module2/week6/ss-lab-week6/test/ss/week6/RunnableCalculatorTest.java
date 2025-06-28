package ss.week6;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.calculator.CalculatorFactory;

import java.io.*;
import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeout;

class RunnableCalculatorTest {
    private CalculatorFactory factory;

    @BeforeEach
    void setup() {
         factory = null; // replace with your own implementation of the factory
    }

    @Test
    void basicTest() throws IOException {
        // We use piped streams here! That means, any write to pw1 is read by pr1; same with pw2 and pr2
        var pr1 = new PipedReader();
        var pw1 = new PipedWriter(pr1);

        var pr2 = new PipedReader();
        var pw2 = new PipedWriter(pr2);

        // run the stream calculator in a separate thread
        var rsc = factory.makeRunnableStreamCalculator(pr1, pw2);
        if (rsc == null) return; // oh, not yet implemented

        var thread = new Thread(rsc);
        thread.start();

        var pw = new PrintWriter(pw1, true);
        var br = new BufferedReader(pr2);

        pw.println("push 0000003");
        pw.println("push -123.00");
        pw.println("add");
        pw.println("pop");
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

        // we close pw and br, this closes pw1 and pr2, this should halt the thread
        pw.close();
        br.close();

        // wait at most 1 second for the thread to stop; if it doesn't, this will trigger an assertion error
        assertTimeout(Duration.ofSeconds(1), () -> {
            thread.join();
        });
    }
}
