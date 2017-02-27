 import java.util.*;
 import java.io.*;

 class Library {
	Map documents = new HashMap();
	Map users = new HashMap();
	Collection loans = new LinkedList();
	final int MAX_NUMBER_OF_LOANS = 20;
 
 public boolean addUser(User user) {
	if (!users.containsValue(user)) {
		users.put (new Integer(user.getCode()), user);
		return true;
	}
	return false;
 }
 
 public boolean removeUser(int userCode) {
	User user = (User)users.get(new Integer(userCode));
	if (user == null || user.numberOfLoans() > 0) return false;
	users.remove(new Integer(userCode));
	return true;
 }
 
 public User getUser(int userCode) {
	return (User)users.get(new Integer(userCode));
 }
 
 public boolean addDocument(Document doc) {
	if (!documents.containsValue(doc)) {
		documents.put(new Integer(doc.getCode()), doc);
		return true;
	}
	return false;
 }
 
 public boolean removeDocument(int docCode) {
	Document doc = (Document)documents.get(new Integer(docCode));
	if (doc == null || doc.isOut()) return false;
	documents.remove(new Integer(docCode));
	return true;
 }
 
 public Document getDocument(int docCode) {
	return (Document)documents.get(new Integer(docCode));
 }
 
 private void addLoan(Loan loan) {
	if (loan == null) return;
	User user = loan.getUser();
	Document doc = loan.getDocument();
	loans.add(loan);
	user.addLoan(loan);
	doc.addLoan(loan);
 }
 
 private void removeLoan(Loan loan) {
	if (loan == null) return;
	User user = loan.getUser();
	Document doc = loan.getDocument() ;
	loans.remove(loan);
	user.removeLoan(loan);
	doc.removeLoan();
 }
 
 public boolean borrowDocument(User user, Document doc) {
	if (user == null || doc == null) return false;
	if (user.numberOfLoans() < MAX_NUMBER_OF_LOANS &&
		doc.isAvailable() && doc.authorizedLoan(user)) {
			Loan loan = new Loan(user, doc);
			addLoan(loan);
			return true;
		}
	return false;
 }
 
 public boolean returnDocument(Document doc) {
	if (doc == null) return false;
	if (doc.isOut()) {
		User user = doc.getBorrower();
		Loan loan = new Loan(user, doc);
		removeLoan(loan);
		return true;
	}
	return false;
 }
 
 public boolean isHolding(User user, Document doc) {
	if (user == null || doc == null) return false;
	return loans.contains(new Loan(user, doc));
 }
 
 public List searchUser(String name) {
	List usersFound = new LinkedList();
	Iterator i = users.values().iterator();
	while (i.hasNext()) {
		User user = (User)i.next();
		if (user.getName().indexOf(name) != -1)
			usersFound.add(user);
	}
	return usersFound;
 }
 
 public List searchDocumentByTitle(String title) {
	List docsFound = new LinkedList();
	Iterator i = documents.values().iterator();
	while (i.hasNext()) {
		Document doc = (Document)i.next();
		if (doc.getTitle().indexOf(title) != -1)
		docsFound.add(doc);
	}
	return docsFound;
 }
 
 public List searchDocumentByAuthors(String authors) {
	List docsFound = new LinkedList();
	Iterator i = documents.values().iterator();
	while (i.hasNext()) {
		Document doc = (Document)i.next();
		if (doc.getAuthors().indexOf(authors) != -1)
			docsFound.add(doc);
		}
	return docsFound;
 }
 
 public int searchDocumentByISBN(String isbn) {
	Iterator i = documents.values().iterator();
	while (i.hasNext()) {
	Document doc = (Document)i.next();
	if (isbn.equals(doc.getISBN()))
		return doc.getCode();
	}
	return -1;
 }
 
 public void printAllLoans() {
	Iterator i = loans.iterator();
	while (i.hasNext()) {
		Loan loan = (Loan)i.next();
		loan.print();
	}
 }
 public void printUserInfo(User user) {
	user.printInfo();
 }
 
 public void printDocumentInfo(Document doc) {
	doc.printInfo();
 }
}