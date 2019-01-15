package group92.spectrangle;

import java.io.*;
import java.net.*;

public class Server {
    private String name;
    private InetAddress address;
    private ServerSocket socket;
    private String ipv4 = "";
    private BufferedReader in;
    private BufferedWriter out;

    public static void main(String[] args) {
        Server server = new Server("bob");
        server.create();
    }

    //Constructor, initializes name and gets the ipv4 address
    public Server(String name) {
        this.name = name;

        try {
            DatagramSocket socket2;
            socket2 = new DatagramSocket();
            socket2.connect(InetAddress.getByName("8.8.8.8"), 10002);
            ipv4 = socket2.getLocalAddress().getHostAddress();
        } catch (SocketException | UnknownHostException e) {
            e.printStackTrace();
        }
    }

    //Creates the server
    public void create() {
        try {
            address = InetAddress.getByName(ipv4);
            socket = new ServerSocket(Game.PORT, 50, address);
//            socket = new ServerSocket(Game.PORT);
            ConnectionHandler connectionHandler = new ConnectionHandler(socket);
            //TODO create thread to receive messages and send messages
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
