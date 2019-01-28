package group92.spectrangle.network;

import group92.spectrangle.Game;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.players.ClientPlayer;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.ClientProtocol;
import group92.spectrangle.view.GUI;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.*;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

public class Client implements ClientProtocol {
    private String name;
    private GUI gui;
    private ClientPlayer player;
    private Game game;
    private String ipv4 = "";
    private ArrayList<ConnectedServer> connectedServers;
    private ConnectedServer joinedServer;

    public static void main(String[] args) {
        Client client = new Client();
//        client.joinServer();
    }

    //creates a client with a name
    public Client() {
        gui = new GUI(this);

        connectedServers = new ArrayList<>();
        //This entire try catch block is to get the ipv4 address
        try {
            DatagramSocket socket2;
            socket2 = new DatagramSocket();
            socket2.connect(InetAddress.getByName("8.8.8.8"), 10002);
            ipv4 = socket2.getLocalAddress().getHostAddress();
        } catch (SocketException | UnknownHostException e) {
            e.printStackTrace();
        }

        gui.start();
    }

    //sets the name of this client and initializes a player object with this name
    public void setName(String name) throws IllegalNameException {
        this.name = name;
        player = new ClientPlayer(name);
    }

    //returns the name of this client
    public String getName() {
        return name;
    }

    //tries to search for a server, if a connection gets made it gets added to the connectedServers list
    public void searchForServer() {
        ConnectedServer connectedServer = new ConnectedServer(this);
        if(connectedServer.joinServer()) {
            connectedServers.add(connectedServer);
        }

    }

    //reads a message and executes the corresponding action
    //@ requires splitMessage != null;
    private void readMessage(String[] splitMessage, ConnectedServer connectedServer) {
        if(splitMessage == null) {
            return;
        }

        String first = splitMessage[0];
        if(first.equals("announce")) {
            //give this server a name
            String serverName = splitMessage[1];
            connectedServer.setName(serverName);
            gui.addServer(connectedServer.getIP(), connectedServer.getSock(), serverName);

        } else if(first.equals("respond")) {
            for(int i = 1; (i + 3) < splitMessage.length; i = i + 3) {
                String gameName = splitMessage[i];
                String maxPlayers = splitMessage[i + 1];
                String joinedPlayers = splitMessage[i + 2];
                //TODO show this in a game list
            }

        } else if(first.equals("give")) {
            String username = splitMessage[1];
            for(int i = 2; (i + 4) < splitMessage.length; i = i + 4) {
                String multiplier = splitMessage[i];
                String color1 = splitMessage[i + 1];
                String color2 = splitMessage[i + 2];
                String color3 = splitMessage[i + 3];
                //TODO give this piece to the player
            }


            } else if(first.equals("turn")) {
            String username = splitMessage[1];
            if(username.equals(player.getName())) {
                //TODO it is your turn, notify client
            } else {
                //TODO possibly notify client whose turn it is
            }

        } else if(first.equals("move")) {
            String username = splitMessage[1];
            String multiplier = splitMessage[2];
            String color1 = splitMessage[3];
            String color2 = splitMessage[4];
            String color3 = splitMessage[5];
            String index = splitMessage[6];
            //TODO make this move on the board and draw it on the GUI

        } else if(first.equals("swap")) {
            String username = splitMessage[1];
            String color1 = splitMessage[2];
            String color2 = splitMessage[3];
            String color3 = splitMessage[4];
            String index = splitMessage[5];
            String secondColor1 = splitMessage[6];
            String secondColor2 = splitMessage[7];
            String secondColor3 = splitMessage[8];
            String secondIndex = splitMessage[9];
            //TODO swap pieces in inventory of this player

        }  else if(first.equals("skip")) {
            String username = splitMessage[1];
            //TODO skip this player's turn

        } else if(first.equals("end")) {
            //TODO

        } else if(first.equals("exception")) {
            //TODO

        } else if(first.equals("message")) {
            //TODO

        }
    }

    @Override
    public String scan() {
        return ClientProtocol.SCAN;
    }

    @Override
    public String connect(Player player) {
        return ClientProtocol.CONNECT + ";" + player.getName();
    }

    @Override
    public String join() {
        return ClientProtocol.JOIN;
    }

    @Override
    public String join(String username) {
        return ClientProtocol.JOIN + ";" + username;
    }

    @Override
    public String join(int maxPlayers) {
        return ClientProtocol.JOIN + ";" + maxPlayers;
    }

    @Override
    public String create() {
        return ClientProtocol.CREATE;
    }

    @Override
    public String create(int maxPlayers) {
        return ClientProtocol.CREATE + ";" + maxPlayers;
    }

    @Override
    public String start() {
        return ClientProtocol.START;
    }

    @Override
    public String move(Tile tile, int index) {
        return ClientProtocol.MOVE + ";" + tile.toString() + index;
    }

    @Override
    public String swap(Tile tile) {
        return ClientProtocol.SWAP + ";" + tile.toString();
    }

    @Override
    public String skip() {
        return ClientProtocol.SKIP;
    }

    @Override
    public String leave() {
        return ClientProtocol.LEAVE;
    }

    @Override
    public String disconnect() {
        return ClientProtocol.DISCONNECT;
    }

    @Override
    public String message(String message) {
        return ClientProtocol.MESSAGE + ";" + message;
    }

    //join a specific server
    //@ requires name != null && address != null && port != null;
    public void joinServer(String name, String address, String port) {
        for(ConnectedServer cs : connectedServers) {
            if(cs.getName().equals(name) && cs.getIP().equals(address) && cs.getSock().equals(port)) {
                joinedServer = cs;
                joinedServer.writeMessage(connect(player));
            }
        }
    }

    //a server that this client is connected to, having this in a separate class allows for the client to connect to multiple servers
    public class ConnectedServer implements Runnable {
        private Socket socket;
        private PrintWriter out;
        private BufferedReader in;
        private InetAddress hostAddress;
        private Client client;
        private String ip;
        private String sock;
        private String name;

        //creates a ConnectedServer object
        //@ requires client != null;
        //@ ensures client == client;
        public ConnectedServer(Client client) {
            this.client = client;
        }

        //returns the socket of the server
        //@ pure
        public String getSock() {
            return sock;
        }

        //returns the ip of the server
        //@ pure
        public String getIP() {
            return ip;
        }

        //returns the name of the server
        //@ pure
        public String getName() {
            return name;
        }

        //sets the name of this server
        //@ requires name != null;
        //@ ensures name == name;
        public void setName(String name) {
            this.name = name;
        }

        //creates a socket and connects to a server socket if one exists on the specified port
        public boolean joinServer() {
            try {
                hostAddress = InetAddress.getByName(ipv4);
                socket = new Socket(hostAddress, Game.PORT);
                ip = socket.getInetAddress().toString();
                sock = String.valueOf(Game.PORT);
                out = new PrintWriter(socket.getOutputStream(), true);
                in = new BufferedReader(new InputStreamReader(socket.getInputStream(), StandardCharsets.UTF_8));
                Thread t = new Thread(this);
                t.start();
                BufferedReader terminalInput = new BufferedReader(new InputStreamReader(System.in));
                System.out.println("[Client] Connected to a server: " + socket.toString());
                writeMessage(scan());
                return true;
                //TODO read terminal input if GUI doesn't work out
//                while(true) {
//                    String command = terminalInput.readLine().toLowerCase();
//                    if(command.equals("q")) {
//                        break;
//                    }
//                    out.println(command);
//                    out.flush();
//                }
//                out.close();
//                in.close();
//                socket.close();
            } catch (IOException e) {
                e.printStackTrace();
                return false;
            }
        }

        //reads the bufferedreader of the serverSocket this client is connected to
        //@requires socket != null;
        @Override
        public void run() {
            while(socket.isConnected()) {
                try {
                    String message = in.readLine();
                    System.out.println("[Client] received message: " + message);
                    String[] splitMessage = message.split(";");
                    client.readMessage(splitMessage, this);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }

        //writes a message to the server
        //@ requires message != null && out != null;
        public void writeMessage(String message) {
            out.println(message);
            out.flush();
        }
    }

}
