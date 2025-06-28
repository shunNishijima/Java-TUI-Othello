package ss.hotel;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class HotelTest {
    /** Test variable for a <tt>Hotel</tt> object. */
    private Hotel hotel;
    public static final String GUEST_NAME_1 = "Major Gowen";
    public static final String GUEST_NAME_2 = "Miss Tibbs";
    public static final String GUEST_NAME_3 = "Miss Gatsby";

    /**
     * Sets the instance variable <tt>hotel</tt> to a well-defined initial value.
     * All test methods should be preceded by a call to this method.
     */
    @BeforeEach
    public void setUp() {
        hotel = new Hotel("U Parkhotel");
    }

    /**
     * checkIn must, as long as rooms are available, return a room occupied by the specified guest.
     * When the hotel is full, checkIn must return null.
     */
    @Test
    public void testCheckIn() {
        Room room1 = hotel.checkIn(GUEST_NAME_1);
        assertNotNull(room1);
        assertNotNull(room1.getGuest());
        assertTrue(room1.getGuest().getRoom() == room1);
        assertEquals(GUEST_NAME_1, room1.getGuest().getName(), "Correct 1st guest check in");

        Room room2 = hotel.checkIn(GUEST_NAME_2);
        assertNotNull(room2);
        assertNotNull(room2.getGuest());
        assertTrue(room2.getGuest().getRoom() == room2);
        assertEquals(GUEST_NAME_2, room2.getGuest().getName(), "Correct 2nd guest check in");

        Room noRoom = hotel.checkIn(GUEST_NAME_3);
        assertNull(noRoom, "No check in when hotel is full");
    }

    /**
     * If the specified guest is checked in, he must be checked out, i.e., afterwards, he must not have a room anymore,
     * and his room must now be empty. The room's safe must be inactivated as well.
     */
    @Test
    public void testCheckoutOccupiedRoom() {
        Room room = hotel.checkIn(GUEST_NAME_1);
        Guest guest = room.getGuest();
        Safe safe = room.getSafe();
        safe.activate();

        hotel.checkOut(GUEST_NAME_1);
        assertNull(guest.getRoom(), "Guest has no room");
        assertNull(room.getGuest(), "Room has no guest");
        assertFalse(safe.isActive(), "Safe is inactive");
    }

    @Test
    public void testCheckoutEmptyRoom() {
        hotel.checkOut(GUEST_NAME_1);
        // nothing to be checked here, but no exception should occur.
    }

    /**
     * If there is a free room, getFreeRoom must return a room without guest.
     */
    @Test
    public void testGetFreeRoomFromNotFullHotel() {
        Room room = hotel.getFreeRoom();
        assertNull(room.getGuest(), "A room is free");

        hotel.checkIn(GUEST_NAME_1);
        Room freeRoom = hotel.getFreeRoom();
        assertNotNull(freeRoom, "Another room is free");
        assertNotEquals(room, freeRoom, "Another room is free");
    }

    /**
     * If there is no free room, getFreeRoom must return null.
     */
    @Test
    public void testGetFreeRoomFromFullHotel() {
        hotel.checkIn(GUEST_NAME_1);
        hotel.checkIn(GUEST_NAME_2);

        Room noRoom = hotel.getFreeRoom();
        assertNull(noRoom, "No room available in a full hotel");
    }

    /**
     * getRoom must not return any room, if the guest is not checked in
     */
    @Test
    public void testGetRoomBeforeCheckIn() {
        Room room = hotel.getRoom(GUEST_NAME_1);
        assertNull(room, "Guest 1 not checked in");
    }

    /**
     * If the guest is checked in, the returned room must be occupied by the specified guest.
     */
    @Test
    public void testGetRoomAfterCheckIn() {
        hotel.checkIn(GUEST_NAME_1);

        Room room = hotel.getRoom(GUEST_NAME_1);
        assertEquals(GUEST_NAME_1, room.getGuest().getName(),"Guest 1 checked in");
    }

    /**
     * ToString is difficult to test fully because there is no restriction on the format of the returned String.
     * At least it can be tested that a String is returned and that it contains the name of a checked in guest.
     */
    @Test
    public void testToString() {
        hotel.checkIn(GUEST_NAME_1);

        assertTrue(hotel.toString().contains(GUEST_NAME_1));
    }
}
