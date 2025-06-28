package ss.week2;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ss.week2.DollarsAndCentsCounter;

/**
 * Test program for Dollars and Cents Counter.
 * Lab Exercise Software Systems.
 * @author Jip Spel
 */
public class DollarsAndCentsCounterTest {
    /** Test variable for a <tt>DollarsAndCentsCounter</tt> object. */
    private DollarsAndCentsCounter counter;

    /**
     * Sets the instance variable <tt>counter</tt> to a well-defined initial value.
     */
    @BeforeEach
    public void setUp() {
        counter = new DollarsAndCentsCounter();
        counter.reset();
    }

    /**
     * Test the method <tt>getDollars()</tt>.
     */
    @Test
    public void testDollars() {
        counter.add(5, 0);
        assertEquals(5, counter.getDollars());
        counter.add(0, 102);
        assertEquals(6, counter.getDollars());
    }

    /**
     * Test the method <tt>cents()</tt>.
     */
    @Test
    public void testCents() {
        counter.add(0, 5);
        assertEquals(5, counter.getCents());
        counter.add(0, 95);
        assertEquals(0, counter.getCents());
    }

    /**
     * Test the method <tt>add(getDollars, cents)</tt>.
     */
    @Test
    public void testAdd() {
        counter.add(0, 10);
        assertEquals(0, counter.getDollars());
        assertEquals(10, counter.getCents());
        counter.add(2, 95);
        assertEquals(3, counter.getDollars());
        assertEquals(5, counter.getCents());
    }

    /**
     * Test the method <tt>reset()</tt>.
     */
    @Test
    public void testReset() {
        counter.add(22, 33);

        counter.reset();
        assertEquals(0, counter.getDollars());
        assertEquals(0, counter.getCents());
    }
}
