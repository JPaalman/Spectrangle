package group92.spectrangle;

import java.io.*;
import java.net.*;
import java.util.ArrayList;

public class Server {
    private String name;
    private InetAddress address;
    private ServerSocket socket;
    private String ipv4 = "";
    private BufferedReader in;
    private BufferedWriter out;
    private ArrayList<ConnectedClient> connectedClients;

    public static void main(String[] args) {
        Server server = new Server("bob");
        server.create();
    }

    //Constructor, initializes name and gets the ipv4 address
    public Server(String name) {
        this.name = name;
        connectedClients = new ArrayList<ConnectedClient>();

        try {
            DatagramSocket socket2;
            socket2 = new DatagramSocket();
            socket2.connect(InetAddress.getByName("8.8.8.8"), 10002);
            ipv4 = socket2.getLocalAddress().getHostAddress();
        } catch (SocketException | UnknownHostException e) {
            e.printStackTrace();
        }
    }

    //Sends a message to all connected clients
    public void forward(String message) {
        for(ConnectedClient client : connectedClients) {
            try {
                client.getWriter().write(message);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    //Creates the server
    public void create() {
        try {
            address = InetAddress.getByName(ipv4);
            socket = new ServerSocket(Game.PORT, 50, address);
//            socket = new ServerSocket(Game.PORT);
            ConnectionHandler connectionHandler = new ConnectionHandler(socket, this);
            connectionHandler.run();
            //TODO create thread to receive messages and send messages
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    //Adds a connected client to the connected clients list
    public void addClient(BufferedReader in, BufferedWriter out, Socket clientSocket) {
        //Make sure we don't have this client yet
        for(ConnectedClient client : connectedClients) {
            if(client.getSocket() == clientSocket) {
                return;
            }
        }
        connectedClients.add(new ConnectedClient(in, out, clientSocket));
    }

    //Removes a client from the connected clients list
    public void removeClient(Socket clientSocket) {
        for(ConnectedClient client : connectedClients) {
            if(client.getSocket() == clientSocket) {
                connectedClients.remove(client);
            }
        }
    }

    public void readMessage(String[] splitMessage, BufferedWriter out) {
        //TODO
    }

    //A class that holds information about a connected player
    public class ConnectedClient {
        private BufferedReader in;
        private BufferedWriter out;
        private Socket socket;

        public ConnectedClient(BufferedReader in, BufferedWriter out, Socket socket) {
            this.in = in;
            this.out = out;
            this.socket = socket;
        }

        public BufferedReader getReader() {
            return in;
        }

        public BufferedWriter getWriter() {
            return out;
        }

        public Socket getSocket() {
            return socket;
        }
    }
}
