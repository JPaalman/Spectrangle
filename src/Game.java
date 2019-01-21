package group92.spectrangle;

public class Game {

    private static final String USAGE = "Usage: <server | client> + <name>";
    public static final int PORT = 2626;
    private static String name;
    private static final int MAXNAMESIZE = 10;

    public static void main(String[] args) {
        System.out.println("test");
        if(args.length < 2) {
            errorMessage("Too few arguments.");
            return;
        } else if(args.length > 2) {
            errorMessage("Too many arguments.");
            return;
        }

        name = args[1];

        if(name.contains(";")) {
            errorMessage("You are not allowed to use ';' in your name.");
            return;
        } else if (name.length() > MAXNAMESIZE) {
            errorMessage("Your name exceeds the maximum size of " + MAXNAMESIZE + " characters.");
            return;
        }

        if(args[0].equals("server")) {
            Server server = new Server(args[1]);
            server.create();
        } else if(args[0].equals("client")) {
            //TODO
            Client client = new Client(args[1]);
            client.join();
        } else {
            errorMessage("Invalid first argument.");
            return;
        }

    }

    public static void errorMessage(String error) {
        System.out.println(error + "\n" + USAGE);
    }

}
