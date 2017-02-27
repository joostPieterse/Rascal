class Book extends Document {

	public Book(String tit, String auth, String isbn) {
		super(tit);
		ISBNCode = isbn;
		authors = auth;
	}

	public void printInfo() {
		printHeader();
		printAuthors() ;
		printGeneralInfo();
		printAvailability();
	}
}
