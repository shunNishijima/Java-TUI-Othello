package ss.week6.threads;

/**
 * ConsumeInteger class for Producer/Consumer program.
 * @author Revirion by Rieks op den Akker
 * @version january 2002
 */
public class IntConsumer implements Runnable {
	private IntCell cell;

	public IntConsumer(int nr, IntCell cellArg) {
		this.cell = cellArg;
	}

	public void run() {
		int val;
		do {
			// sleep for a random interval
			try {
				Thread.sleep((int) (Math.random() * 3000));
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			val = cell.getValue();
			System.out.println(Thread.currentThread().getName() 
					+ ": " + val + " read");
		} while (val != -1);

		System.out.println(Thread.currentThread().getName() + ": end");
	}
}

/**************************************************************************
 * (C) Copyright 1999 by Deitel & Associates, Inc. and Prentice Hall.     *
 * All Rights Reserved.                                                   *
 *                                                                        *
 * DISCLAIMER: The authors and publisher of this book have used their     *
 * best efforts in preparing the book. These efforts include the          *
 * development, research, and testing of the theories and programs        *
 * to determine their effectiveness. The authors and publisher make       *
 * no warranty of any kind, expressed or implied, with regard to these    *
 * programs or to the documentation contained in these books. The authors *
 * and publisher shall not be liable in any event for incidental or       *
 * consequential damages in connection with, or arising out of, the       *
 * furnishing, performance, or use of these programs.                     *
 *************************************************************************/
