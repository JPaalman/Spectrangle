package group92.spectrangle.network;

import group92.spectrangle.Game;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.players.ClientPlayer;
import group92.spectrangle.players.ComputerPlayer;
import group92.spectrangle.players.NetworkPlayer;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.ClientProtocol;
import group92.spectrangle.protocol.Protocol;
import group92.spectrangle.view.GUI;

import java.awt.*;
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
    private Player player;
    private Game game;
    private String ipv4 = "";
    private ArrayList<ConnectedServer> connectedServers;
    private ConnectedServer joinedServer;

    //starts this program from the client-side
    public static void main(String[] args) {
        new Client();
    }

    //sets the game with the player count
    //@ ensures this.game != null;
    //@ ensures this.game.getMaxPlayerCount() <= 4 && this.game.getMaxPlayerCount() >= 2;
    //@ ensures playerCount <=4 && playerCount >= 2 => this.game.getMaxPlayerCount() == playerCount;
    public void setGame(int playerCount) {
        if (playerCount > 4) {
            playerCount = 4;
        } else if (playerCount < 2) {
            playerCount = 2;
        }
        game = new Game(playerCount);
    }

    //returns the game object
    //@ requires this.game != null;
    //@ pure
    public Game getGame() {
        return game;
    }

    //returns the player object
    // @ requires this.player != null;
    //@ pure
    public Player getPlayer() {
        return player;
    }

    //creates a client with a name, a gui, a list of connected servers
    //@ ensures this.gui != null;
    //@ ensures this.connectedServers != null;
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
    //@ requires name != null && name.length() > 2 && !name.contains(";");
    //@ ensures this.name = name && this.player != null;
    //@ ensures this.player.getName() = name;

    public void setName(String name) throws IllegalNameException {
        this.name = name;
        if (gui.getBot()) {
            player = new ComputerPlayer(name);
        } else {
            player = new ClientPlayer(name);
        }
    }

    //returns the name of this client
    //@ requires this.name != null;
    //@ pure
    public String getName() {
        return name;
    }

    //tries to search for a server, if a connection gets made it gets added to the connectedServers list
    //@ requires ipv4 != null;
    public void searchForServer() {
        searchForServer(ipv4);
    }

    //tries to search for a server, if a connection gets made it gets added to the connectedServers list
    //@ requires address != null && connectedServers != null;
    public void searchForServer(String address) {
        ConnectedServer connectedServer = new ConnectedServer(this);
        if(connectedServer.joinServer(address)) {
            connectedServers.add(connectedServer);
        }
    }

    //reads a message and executes the corresponding action
    //@ requires splitMessage != null && connectedServer != null;
    private void readMessage(String[] splitMessage, ConnectedServer connectedServer) {
        if(splitMessage == null) {
            return;
        }
        String first = splitMessage[0];
        switch (first) {
            case "announce":
                //give this server a name
                String serverName = splitMessage[1];
                connectedServer.setName(serverName);
                gui.addServer(connectedServer.getIP(), connectedServer.getSock(), serverName);

                break;
            case "respond":
                //add games to the game list

                for (int i = 1; (i + 2) < splitMessage.length; i = i + 3) {
                    String gameName = splitMessage[i];
                    String maxPlayers = splitMessage[i + 1];
                    String joinedPlayers = splitMessage[i + 2];
                    gui.addGameToList(gameName, maxPlayers, joinedPlayers);
                }

                break;
            case "give": {
                //give a piece to a player in your game
                String username = splitMessage[1];
                Player p = null;

                if(game.getPlayer(username) == null) { //if we don't know of this player yet create this player and add him to the game
                    try {
                        p = new NetworkPlayer(username);
                        game.addPlayer(p);
                    } catch (IllegalNameException e) {
                        e.printStackTrace(); //should not happen
                    }
                } else {
                    p = game.getPlayer(username);
                }

                for (int i = 2; i < splitMessage.length; i = i + 4) {
                    int multiplier = Integer.parseInt(splitMessage[i]);
                    Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 1]);
                    Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 2]);
                    Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 3]);
                    Tile tile = new Tile(multiplier, c1, c2, c3);
                    p.addPiece(tile);
                    game.getBag().removePiece(tile);
                }
                gui.updateInventory(game.getPlayers());
                break;

            }
            case "turn": {
                //notify GUI whose turn it is
                String username = splitMessage[1];
                if (username.equals(name) && player instanceof ComputerPlayer) {
                    String move = ((ComputerPlayer) player).getMove(game.getBoard());
                    if (move.equals("skip")) {
                        if (!game.getBag().isEmpty()) {
                            connectedServer.writeMessage(swap(player.getInventory().get((int) Math.random() * player.getInventory().size())));
                        } else {
                            connectedServer.writeMessage(move);
                        }
                    } else {
                        connectedServer.writeMessage(move);
                    }
                }
                gui.notifyTurn(username);
                break;
            }
            case "move": {
                //make a move in your game
                String username = splitMessage[1];
                int multiplier = Integer.parseInt(splitMessage[2]);
                Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
                Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
                Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[5]);
                int index = Integer.parseInt(splitMessage[6]);
                Tile tile = new Tile(multiplier, c1, c2, c3);
                try {
                    game.getPlayer(username).makeMove(game.getBoard(), tile, index);
                    gui.updateInventory(game.getPlayers());
                } catch (MoveException e) {
                    System.out.println("[Client] invalid move"); //should not happen
                    e.printStackTrace();
                }
                gui.drawMove(tile, index);
                break;
            }
            case "swap": {
                //swap pieces for a player in your game
                String username = splitMessage[1];

                int multiplier = Integer.parseInt(splitMessage[2]);
                Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
                Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
                Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[5]);
                Tile oldTile = new Tile(multiplier, c1, c2, c3);
                multiplier = Integer.parseInt(splitMessage[6]);
                c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[7]);
                c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[8]);
                c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[9]);
                Tile newTile = new Tile(multiplier, c1, c2, c3);
                Player player = game.getPlayer(username);
                player.removePiece(oldTile);
                game.getBag().removePiece(newTile);
                game.getBag().addPiece(oldTile);
                player.addPiece(newTile);
                gui.updateInventory(game.getPlayers());

                break;
            }
            case "skip": {
                //skip a turn of a player in your game
                String username = splitMessage[1];
                gui.skipTurn(username);

                break;
            }
            case "end":
                //the game you are currently in and show the winners
                String winners = splitMessage[1];
                for (int i = 2; i < splitMessage.length; i++) {
                    winners += " and " + splitMessage[i];
                }
                gui.announceWinners(winners);

                break;
            case "exception":
                //exception thrown by the server
                gui.exception(splitMessage[1]);

                break;
            case "message": {
                //a message from a player in your game
                String username = splitMessage[1];
                String message = splitMessage[2];
                gui.addMessage(username, message);

                break;
            }
            case "join": {
                //someone joined the game you are in
                String username = splitMessage[1];
                if (username.equals(name)) {

                } else {
                    Player newPlayer = null;
                    try {
                        newPlayer = new NetworkPlayer(username);
                    } catch (IllegalNameException e) {
                        e.printStackTrace();//should not happen
                    }
                    game.addPlayer(newPlayer);
                }
                break;
            }

            case "leave" : {
                //someone left the game you are in
                String username = splitMessage[1];
                game.removePlayer(game.getPlayer(username));
                gui.updateInventory(game.getPlayers());
            }
        }
    }

    //--------- all commands for the protocol ---------

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
        return ClientProtocol.MOVE + ";" + tile.toString() + ";" + index;
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

    //--------- end of commands for the protocol ---------

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

    //get the connected server with a specific name, address, and port
    //@ requires name != null && address != null && port != null && connectedServers != null;
    public ConnectedServer getConnectedServer(String name, String address, String port) {
        for(ConnectedServer cs : connectedServers) {
            if(cs.getName().equals(name) && cs.getIP().equals(address) && cs.getSock().equals(port)) {
                return cs;
            }
        }
        return null;
    }

    //a server that a client is connected to
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
        //@ ensures this.client == client;
        public ConnectedServer(Client client) {
            this.client = client;
        }

        //returns the socket of the server
        //@ requires this.sock != null;
        //@ pure
        public String getSock() {
            return sock;
        }

        //returns the ip of the server
        //@ requires this.ip != null;
        //@ pure
        public String getIP() {
            return ip;
        }

        //returns the name of the server
        //@ requires this.name != null;
        //@ pure
        public String getName() {
            return name;
        }

        //sets the name of this server
        //@ requires name != null;
        //@ ensures this.name == name;
        public void setName(String name) {
            this.name = name;
        }

        //creates a socket and connects to a server socket if one exists on the specified port
        //@ requires address != null;
        public boolean joinServer(String address) {
            try {
                hostAddress = InetAddress.getByName(address);
                socket = new Socket(hostAddress, Server.PORT);
                ip = socket.getInetAddress().toString();
                sock = String.valueOf(Server.PORT);
                out = new PrintWriter(socket.getOutputStream(), true);
                in = new BufferedReader(new InputStreamReader(socket.getInputStream(), StandardCharsets.UTF_8));
                Thread t = new Thread(this);
                t.start();
                BufferedReader terminalInput = new BufferedReader(new InputStreamReader(System.in));
                System.out.println("[Client] Connected to a server: " + socket.toString());
                writeMessage(scan());
                return true;
            } catch (IOException e) {
                e.printStackTrace();
                return false;
            }
        }

        //reads the bufferedreader of the serverSocket this client is connected to
        //@ requires this.socket != null;
        //@ requires this.client != null;
        @Override
        public void run() {
            while(!socket.isClosed()) {
                try {
                    String message = in.readLine();
                    System.out.println("[Client] received message: " + message);
                    String[] splitMessage = message.split(";");
                    client.readMessage(splitMessage, this);
                } catch (IOException e) {
                    System.out.println("Server disconnected");
                    disconnect();
                }
            }
        }

        //disconnects from the bufferedreader, the printwriter, and the socket
        //@ requires this.in != null && this.out != null && this.socket != null;
        public void disconnect() {
            try {
                in.close();
                out.close();
                socket.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        //writes a message to the server
        //@ requires message != null && this.out != null;
        public void writeMessage(String message) {
            out.println(message);
            out.flush();
        }
    }

}
