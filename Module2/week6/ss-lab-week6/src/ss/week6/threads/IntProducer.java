package ss.week6.threads;

/**
 * ProduceInteger class for Producer/Consumer program.
 * @author Revision by Rieks op den Akker
 * @version january 2002
 */

public class IntProducer implements Runnable {
	private int nr;
	private IntCell cell;

	public IntProducer(int nrArg, IntCell cellArg) {
		this.nr = nrArg;
		this.cell = cellArg;
	}

	public void run() {
		for (int i = 0; i < 10; i++) {
			try {
				Thread.sleep((int) (Math.random() * 3000));
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			int val = 10 * nr + i;
			System.out.println(Thread.currentThread().getName() 
					+ ": " + val + " written");
			cell.setValue(val);
		}

		System.out.println(Thread.currentThread().getName() 
				+ ": end");
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
