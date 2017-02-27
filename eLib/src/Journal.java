class Journal extends Document {
	
	public Journal(String tit ) {
		super(tit);
	}
	public boolean authorizedLoan(User user) {
		return user.authorizedUser();
	}
}