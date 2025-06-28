package ss.week6;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import ss.week6.cards.Card;

import java.io.*;

/**
 * Testprogram for the write and read methods in Card.
 * Lab Exercise SoftwareSystems
 * @author Jip Spel
 * @version $Revision: 1.0 $
 */
public class CardTest {

    /** Testvariabele for a <tt>Card</tt> object. */
    private Card card;

    /** Path to where you will save the card files */
    private static final String PATH = ""; //Your path to the test folder

    @BeforeEach
    public void setUp() {
        card = new Card('H', 'J');
    }

    /** Test for writing and reading a card with text files.*/
    @Test
    public void testReadingWritingFiles() {
        try {
            PrintWriter writer = new PrintWriter(new FileWriter(PATH + "card.txt"));
            card.write(writer);
            writer.close();

            BufferedReader reader = new BufferedReader(new FileReader(PATH + "card.txt"));
            Card card2 = Card.read(reader);
            reader.close();
            assertEquals(card, card2);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
