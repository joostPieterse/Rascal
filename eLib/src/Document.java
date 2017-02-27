 import java.util.*;
 class Document {
	int documentCode;
	String title;
	String authors;
	String ISBNCode;
	Loan loan = null;
	static int nextDocumentCodeAvailable = 0;
 
	public Document(String tit) {
		title = tit;
		ISBNCode = "";
		authors = "";
		documentCode = Document.nextDocumentCodeAvailable++;
	}
 
	public boolean equals(Object obj) {
		Document doc = (Document)obj;
		return documentCode == doc.documentCode;
	}
	
	public boolean isAvailable() {
		return loan == null;
	}
 
	public boolean isOut() {
		return !isAvailable() ;
	}

    public boolean authorizedLoan(User user) {
       return true;
    }

     public User getBorrower() {
       if (loan != null)
         return loan.getUser();
       return null;
     }

     public int getCode() {
       return documentCode;
     }

     public String getTitle() {
       return title;
     }

     public String getAuthors() {
       return authors;
     }

     public String getISBN() {
       return ISBNCode;
     }

     public void addLoan(Loan ln) {
       loan =  ln;
     }

     public void removeLoan() {
       loan = null;
     }

     protected void printAuthors() {
       System.out.println("Author(s): " + getAuthors());
     }

     protected void printHeader() {
       System.out.println("Document: " +  getCode() +
           " - " + getTitle());
     }

	protected void printAvailability() {
		if (loan == null) {
			System.out.println("Available.");
		} else {
			User user= loan.getUser();
			System.out.println("Hold by " +  user.getCode() +
				" - " +  user.getName());	
		}
	}

	protected void printGeneralInfo() { 
		System.out.println("Title: "+ getTitle()); 
			if (!getISBN().equals(""))
				System.out.println("ISBN:  " +  getISBN());
	}
	
	public void printInfo() {
		printHeader(); 
		printGeneralInfo(); 
		printAvailability();
	}
}
