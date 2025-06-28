package ss.hotel;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class RoomTest {
    private Guest guest;
    private Room room;
    
    @BeforeEach
    public void setUp() {
        guest = new Guest("Jip");
         // TODO: initialise the variable room
    }

    @Test
    public void testSetUp() {
        assertEquals(101, room.getNumber());
    }

    @Test
    public void testSetGuest() {
        room.setGuest(guest);
        assertEquals(guest, room.getGuest());
    }
    
}
