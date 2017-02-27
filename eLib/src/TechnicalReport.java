 class TechnicalReport extends Document {
	String refNo;

	public TechnicalReport(String tit, String ref, String auth) {
		super(tit);
		refNo = ref;
		authors = auth;
	}
	
	public boolean authorizedLoan(User user) {
		return false;
	}
 
	public String getRefNo() {
		return refNo;
	}
 
	protected void printRefNo() {
		System.out.println( "Ref . No.: " + getRefNo());
	}
 
	public void printInfo() {
		printHeader();
		printAuthors();
		printGeneralInfo();
		printRefNo();
	}
 }
 
 