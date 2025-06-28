package ss.week6.account;

public class Account {
	protected double balance = 0.0;

	public void transaction(double amount) {
		balance = balance + amount;
	}
	public double getBalance() {
		return balance;

	}
}
