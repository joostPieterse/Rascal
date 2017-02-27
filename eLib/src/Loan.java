 class Loan {
 User user;
 Document document;
 
 public Loan(User usr, Document doc) {
	user = usr;
	document = doc;
 }
 
 public User getUser() {
	return user;
 }
 
 public Document getDocument() {
	return document;
 }
 
 public boolean equals(Object obj) {
	Loan loan = (Loan)obj;
	return user.equals(loan.user) && document.equals(loan.document);
 }
 
 public void print() {
	System.out.println("User: " + user.getCode() +
	" - " + user.getName() +
	" holds doc: " + document.getCode() +
	" - " + document. getTitle());
 }
 
 }