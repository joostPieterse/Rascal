	import java.util.*;
	import java.io.*;

	class Main {
     static Library lib = new Library();

     public static void printHeader() {
       System.out.println("COMMANDS:");
       System.out.println("addUser name, address, phone");
       System.out.println("addintUser name, address, phone, id");
       System.out.println("rmUser userid");
       System.out.println("addBook title, authors, ISBN");
       System.out.println("addReport title, ref, authors");
       System.out.println("addJournal title");
       System.out.println("rmDoc docid");
       System.out.println("borrowDoc userid, docid");
       System.out.println("returnDoc docid");
       System.out.println("searchUser name");
       System.out.println("searchDoc title");
       System.out.println("isHolding userid, docid");
       System.out.println("printLoans");
       System.out.println("printUser userid");
       System.out.println("printDoc docid");
       System.out.println("exit");
     }

     public static String[] getArgs(String cmd) {
       String args[] = new String[0];
       String s =  cmd.trim();
       if (s.indexOf(" ")   != -1) {
         s = s.substring(s.indexOf(" "));
         args = s.trim().split(",");
         for (int i = 0 ; i < args.length; i++)
          args[i] = args[i].trim();
       }
       return args;
     }

     public static void addUser(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 3) return;
       User user= new User(args[0], args[1], args[2]);
       lib.addUser(user);
       System.out.println("Added user: "     + user.getCode() +
       " - "     + user.getName());
     }

     public static void addintUser(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 4)return;
       User user = new InternalUser(args[0], args[1], args[2], args[3]);
       lib.addUser(user);
       System.out.println("Added user: "    + user.getCode() +
       " - " + user.getName());
     }

     public static void rmUser(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 1) return;
       User user = lib.getUser(Integer.parseInt(args[0]));
       if (lib.removeUser(Integer.parseInt(args[0])))
         System.out.println(" Removed user: "     + user.getCode() +
         " - "     + user.getName());
     }

     public static void addBook(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 3)return;
       Document doc= new Book(args[0], args[1], args[2]);
       lib.addDocument(doc);
       System.out.println( " Added doc: "    + doc.getCode() +
       "  - "    + doc.getTitle());
     }

   public static void addReport(String cmd) {
      String args[] = getArgs(cmd);
      if (args.length < 3)return;
      Document doc= new TechnicalReport(args[0], args[1], args[2]);
      lib.addDocument(doc);
      System.out.println(" Added doc: "    + doc.getCode() +
      " - "       + doc.getTitle());
    }

    public static void addJournal(String cmd){
      String args[] = getArgs(cmd);
      if (args.length < 1)return;
      Document doc= new Journal(args[0]);
      lib.addDocument(doc);
      System.out.println(" Added doc: "      + doc.getCode() +
      " - "    + doc.getTitle());
     }

    public static void rmDoc(String cmd){
      String args[] = getArgs(cmd);
      if (args.length < 1)return;
      Document doc= lib.getDocument(Integer.parseInt(args[0]));
      if (lib.removeDocument(Integer.parseInt(args[0])))
        System.out.println(" Removed doc: "     + doc.getCode() +
        "  - "     + doc.getTitle());
    }

    public static void borrowDoc(String cmd){
      String args[] = getArgs(cmd);
      if (args.length < 2)return;
      User user= lib.getUser(Integer.parseInt(args[0]));
      Document doc = lib.getDocument(Integer.parseInt(args[1]));
      if (user == null || doc == null) return;
      if (lib.borrowDocument(user, doc))
        System.out.println(" New loan: "      + user.getName() +
        " - "     + doc.getTitle());
    }

    public static void returnDoc(String cmd){
      String args[] = getArgs(cmd);
      if (args.length < 1)return;
      Document doc= lib.getDocument(Integer.parseInt(args[0]));
      if (doc == null)return;
      User user= doc.getBorrower();
      if (user == null)return;
      if (lib.returnDocument(doc))
        System.out.println(" Loan closed: "      + user.getName() +
        " - "     + doc.getTitle());
    }

     public static void searchUser(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 1)return;
       List users = lib.searchUser(args[0]);
       Iterator i = users.iterator();
       while (i.hasNext()) {
        User user = (User)i.next();
        System.out.println("User  found: " + user.getCode() +
         " - " + user.getName());
       }
     }

     public static void searchDoc(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 1)return;
       List docs = lib.searchDocumentByTitle(args[0]);
       Iterator i = docs.iterator();
       while (i.hasNext()) {
        Document doc= (Document)i.next();
         System.out.println("Doc found: " + doc.getCode() +
         "- "+ doc.getTitle());
       }
     }

     public static void isHolding(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 2)return;
       User user= lib.getUser(Integer.parseInt(args[0]));
       Document doc= lib.getDocument(Integer.parseInt(args[1]));
       if (lib.isHolding(user, doc))
         System.out.println(user.getName() +
          " is holding"+ doc.getTitle());
       else
         System.out.println(user.getName() +
          " is not holding " + doc.getTitle());
     }

     public static void printUser(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 1)return;
       User user= lib.getUser(Integer.parseInt(args[0]));
       if (user != null)
        user.printInfo();
     }

     public static void printDoc(String cmd) {
       String args[] = getArgs(cmd);
       if (args.length < 1) return;
       Document doc= lib.getDocument(Integer.parseInt(args[0]));
       if (doc != null)
        doc.printInfo();
     }

	public static  void  dispatchCommand(String cmd)   {
        if (cmd.startsWith("addUser"))  addUser(cmd);
        if (cmd.startsWith("addintUser"))  addintUser(cmd);
		if (cmd.startsWith("rmUser")) rmUser(cmd);
		if (cmd.startsWith("addBook"))  addBook(cmd);
		if (cmd.startsWith("addReport"))  addReport(cmd);
		if (cmd.startsWith("addJournal"))  addJournal(cmd);
		if (cmd.startsWith("rmDoc"))  rmDoc(cmd);
		if (cmd.startsWith("borrowDoc"))  borrowDoc(cmd);
		if (cmd.startsWith("returnDoc"))  returnDoc(cmd);
		if (cmd.startsWith("searchUser"))  searchUser(cmd);
		if (cmd.startsWith("searchDoc"))  searchDoc(cmd);
		if (cmd.startsWith("isHolding"))  isHolding(cmd);
		if (cmd.startsWith("printLoans"))  lib.printAllLoans();
		if (cmd.startsWith("printUser"))  printUser(cmd);
		if (cmd.startsWith("printDoc"))  printDoc(cmd);
     }

    public static  void main(String arg[])   {
		try{
			printHeader();
			String  s =   "";
			BufferedReader in  = new  BufferedReader(
				new  InputStreamReader(System.in));
			while (!s.equals("exit"))  {
				s = in.readLine();
				dispatchCommand(s);
			}
		} catch  (IOException e)  {
			System.err.println("IO error.");
			System.exit(1);
		}
    }
 }

