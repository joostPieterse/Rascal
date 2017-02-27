 class InternalUser extends User {

 String internalld;

 public InternalUser(String name, String addr, String phone, String id) {
	super(name, addr, phone);
	internalld = id;
 }
 
 public boolean authorizedUser() {
	return true;
 }
}