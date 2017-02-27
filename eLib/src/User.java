 import java.util.*;
 
 class User {
	int userCode;
	String fullName;
	String address;
	String phoneNumber;
	Collection loans = new LinkedList();
	static int nextUserCodeAvailable = 0;
 
	public User(String name, String addr, String phone) {
		fullName = name;
		address = addr;
		phoneNumber = phone;
		userCode = User.nextUserCodeAvailable++;
	}

	public boolean equals(Object obj) {
		User user = (User)obj;
		return userCode == user.userCode;
	}
	
	public boolean authorizedUser() {
		return false;
	}
	
	public int getCode() {
		return userCode;
	}
 
	public String getName() {
		return fullName;
	}
 
	public String getAddress() {
		return address;
	}
 
	public String getPhone() {
		return phoneNumber;
	}
 
	public void addLoan(Loan loan) {
		loans.add(loan);
	}
 
	public int numberOfLoans() {
		return loans.size();
	}
 
	public void removeLoan(Loan loan) {
		loans.remove(loan);
	}
 
	public void printInfo() {
		System.out.println ("User: " + getCode() + " - " + getName());
		System.out.println("Address: " + getAddress());
		System.out.println ("Phone: " + getPhone());
		System.out.println("Borrowed documents:");		
		Iterator i = loans.iterator();
		while (i.hasNext()) {
			Loan loan = (Loan)i.next();
			Document doc = loan.getDocument();
			System.out.println(doc.getCode() + " - " + doc.getTitle());
		}	
	}
 }
 