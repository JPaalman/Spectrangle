package group92.spectrangle;

import java.io.*;
import java.net.*;
import java.util.ArrayList;

import static java.lang.Thread.sleep;

public class Server {
    private String name;
    private InetAddress address;
    private ServerSocket socket;
    private String ipv4 = "";
    private ArrayList<ConnectedClient> connectedClients;

    public static void main(String[] args) {
        Server server = new Server("bob");
        server.create();
    }

    //Constructor, initializes name and gets the ipv4 address
    public Server(String name) {
        this.name = name;
        connectedClients = new ArrayList<ConnectedClient>();

        //this try catch block gets the ipv4 address
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
            client.writeMessage(message);
        }
    }

    //Creates the server
    public void create() {
        try {
            address = InetAddress.getByName(ipv4);
//            socket = new ServerSocket(Game.PORT, 50, address);
            socket = new ServerSocket(Game.PORT);
            System.out.println("serversocket: " + socket.toString());
//            socket = new ServerSocket(Game.PORT);
            ConnectionHandler connectionHandler = new ConnectionHandler(socket, this);
            Thread t = new Thread(connectionHandler);
            t.start();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    //Adds a connected client to the connected clients list and starts a thread that listens for incoming messages
    public void addClient(Socket clientSocket) {
        //Make sure we don't have this client yet
        for(ConnectedClient client : connectedClients) {
            if(client.getSocket() == clientSocket) {
                return;
            }
        }
        System.out.println("adding client to list");
        ConnectedClient client = new ConnectedClient(clientSocket, this);
        connectedClients.add(client);
        //TODO send this client the server name
        System.out.println("client added succesful");
        try {
            sleep(100);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        client.writeMessage("test");
        Thread t = new Thread(client);
        t.start();
        System.out.println("thread to read incoming started");
    }

    //Removes a client from the connected clients list
    public void removeClient(ConnectedClient client) {
        for(ConnectedClient c : connectedClients) {
            if(client == c) {
                connectedClients.remove(client);
            }
        }
    }

    public void readMessage(String[] splitMessage, ConnectedClient client) {
        //TODO
    }

    //A class that holds information about a connected player
    public class ConnectedClient implements Runnable {
        private Socket socket;
        private BufferedReader in;
        private PrintWriter out;
        private Server server;

        public ConnectedClient(Socket socket, Server server) {
            this.socket = socket;
            this.server = server;
            try {
                in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                out = new PrintWriter(socket.getOutputStream(), true);
                System.out.println("initialised writer/reader");
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        public String read() {
            try {
                System.out.println("waiting for message: " + in.toString() + " on socket " + socket.toString());
                String message = in.readLine();
                System.out.println("received message: " + message);
                return message;
            } catch (IOException e) {
                e.printStackTrace();
            }
            return"error";
        }

        public void writeSplitMessage(String[] splitMessage) {
            String message = "";
            for(int i = 0; i < splitMessage.length; i++) {
                if(i == splitMessage.length - 1) {
                    message += splitMessage[i];
                } else {
                    message += splitMessage[i] + ";";
                }
            }
            out.println(message);
            out.flush();
        }

        public void writeMessage(String message) {
            System.out.println("sending: " + message + " " + out.toString() + " to socket: " + socket.toString());
            out.println(message);
            out.flush();;

        }

        public BufferedReader getReader() {
            return in;
        }

        public PrintWriter getWriter() {
            return out;
        }

        public Socket getSocket() {
            return socket;
        }

        @Override
        public void run() {
            while(socket.isConnected()) {
                System.out.println("loop");
                String message = read();
                System.out.println(message);
                String[] splitMessage = message.split(";");
                server.readMessage(splitMessage, this);
            }
            server.removeClient(this);
        }
    }
}
