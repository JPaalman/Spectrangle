package group92.spectrangle.network;

import group92.spectrangle.Game;
import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.players.ClientPlayer;
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
    private ClientPlayer player;
    private Game game;
    private String ipv4 = "";
    private ArrayList<ConnectedServer> connectedServers;
    private ConnectedServer joinedServer;

    public static void main(String[] args) {
        Client client = new Client();
//        client.joinServer();
    }

    //sets the game with the player count
    //@ ensures game != null;
    //@ requires playerCount <= 4 && playerCount >= 2;
    public void setGame(int playerCount) {
        game = new Game(playerCount);
        //TODO throw exception for invalid playercount
    }

    //returns the game object
    //@ requires game != null;
    public Game getGame() {
        return game;
    }

    public ClientPlayer getPlayer() {
        return player;
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
        searchForServer(ipv4);
    }

    //tries to search for a server, if a connection gets made it gets added to the connectedServers list

    public void searchForServer(String address) {
        ConnectedServer connectedServer = new ConnectedServer(this);
        if(connectedServer.joinServer(address)) {
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
            for(int i = 1; (i + 2) < splitMessage.length; i = i + 3) {
                String gameName = splitMessage[i];
                String maxPlayers = splitMessage[i + 1];
                String joinedPlayers = splitMessage[i + 2];
                gui.addGameToList(gameName, maxPlayers, joinedPlayers);
            }

        } else if(first.equals("give")) {
            String username = splitMessage[1];
            for(int i = 2; i < splitMessage.length; i = i + 4) {
                int multiplier = Integer.parseInt(splitMessage[i]);
                Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 1]);
                Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 2]);
                Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[i + 3]);
                Tile tile = new Tile(multiplier, c1, c2, c3);
                if(game.getPlayer(username) == null) {
                    for(Player p : game.getPlayers()) {
                        if(p.getName() == null) {
                            p.setName(username);
                            p.addPiece(tile);
                        }
                    }
                } else {
                    game.getPlayer(username).addPiece(tile);
                }
                gui.updateInventory(game.getPlayers());
            }


            } else if(first.equals("turn")) {
            String username = splitMessage[1];
            gui.notifyTurn(username);

        } else if(first.equals("move")) {
            String username = splitMessage[1];
            int multiplier = Integer.parseInt(splitMessage[2]);
            Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
            Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
            Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[5]);
            int index = Integer.parseInt(splitMessage[6]);

            Tile tile = new Tile(multiplier, c1, c2, c3);
            try {
                game.getPlayer(username).makeMove(game.getBoard(), tile, index);
            } catch (MoveException e) {
                System.out.println("[Client] invalid move"); //should not happen
                e.printStackTrace();
            }
//            try {
//                game.getBoard().place(tile, index);
//            } catch (MoveException e) {
//                e.printStackTrace();//should not happen, if it does server is implemented wrong
//            }
            gui.drawMove(tile, index);

        } else if(first.equals("swap")) {
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
            player.addPiece(newTile);
            gui.updateInventory(game.getPlayers());

        }  else if(first.equals("skip")) {
            String username = splitMessage[1];
            gui.skipTurn(username);

        } else if(first.equals("end")) {
            String winners = splitMessage[1];
            for(int i = 2; i < splitMessage.length; i++) {
                winners+=  " and " + splitMessage[i];
            }
            gui.announceWinners(winners);

        } else if(first.equals("exception")) {
            gui.exception(splitMessage[1]);

        } else if(first.equals("message")) {
            String username = splitMessage[1];
            String message = splitMessage[2];
            gui.addMessage(username, message);

        } else if(first.equals("join")) {
            String username = splitMessage[1];
            if(username.equals(name)) {

            } else {
                Player newPlayer = new NetworkPlayer();
                newPlayer.setName(username);
                game.addPlayer(newPlayer);
            }
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

    public ConnectedServer getConnectedServer(String name, String address, String port) {
        for(ConnectedServer cs : connectedServers) {
            if(cs.getName().equals(name) && cs.getIP().equals(address) && cs.getSock().equals(port)) {
                return cs;
            }
        }
        return null;
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
        public boolean joinServer(String address) {
            try {
                hostAddress = InetAddress.getByName(address);
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
