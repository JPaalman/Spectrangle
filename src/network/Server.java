package group92.spectrangle.network;

import group92.spectrangle.Game;
import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.exceptions.MoveException;
import group92.spectrangle.players.NetworkPlayer;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.Protocol;
import group92.spectrangle.protocol.ServerProtocol;

import java.awt.*;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

import static group92.spectrangle.board.Board.getCoordinatesFromIndex;
import static java.lang.Thread.sleep;

public class Server implements ServerProtocol {
    private String name;
    private ServerSocket socket;
    private ArrayList<ConnectedClient> connectedClients;
    private ArrayList<Game> games;

    public static void main(String[] args) {
        try {
            Server server = new Server("bob");
            server.create();
        } catch (IllegalNameException e) {
            System.out.println("Illegal server name");
        }
    }

    //Constructor, initializes name and gets the ipv4 address
    //@ requires name != null;
    //@ ensures !name.contains(";") => name != null;
    //@ ensures connectedClients != null && games != null;
    public Server(String name) throws IllegalNameException {
        if(!name.contains(";")) {
            this.name = name;
        } else {
            throw new IllegalNameException(name + " illegal name");
        }
        connectedClients = new ArrayList<>();
        games = new ArrayList<>();
    }

    //Sends a message to all connected clients
    //@ requires message != null && connectedClients != null;
    public void forward(String message) {
        for(ConnectedClient client : connectedClients) {
            client.writeMessage(message);
        }
    }

    //sends a message to all connected clients in a game
    public void forwardToGame(String message, ConnectedClient client) {
        for(ConnectedClient c : connectedClients) {
            if(client.getGame() == c.getGame()) {
                c.writeMessage(message);
            }
        }
    }

    //Creates the server
    public void create() {
        try {
            socket = new ServerSocket(Game.PORT);
            ConnectionHandler connectionHandler = new ConnectionHandler(socket, this);
            Thread t = new Thread(connectionHandler);
            t.start();
        } catch (IOException e) {
            System.out.println("[Server] could not open server socket");
            e.printStackTrace();
        }
    }

    //Adds a connected client to the connected clients list and starts a thread that listens for incoming messages
    //@ requires clientSocket != null;
    //@ ensures connectedClients.contains(clientSocket);
    public void addClient(Socket clientSocket) {
        //Make sure we don't have this client yet
        for(ConnectedClient client : connectedClients) {
            if(client.getSocket() == clientSocket) {
                return;
            }
        }
        ConnectedClient client = new ConnectedClient(clientSocket, this);
        connectedClients.add(client);
        try {
            sleep(100);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        client.writeMessage(name);
        Thread t = new Thread(client);
        t.start();
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
        if(splitMessage == null || client == null) {
            return;
        }

        String first = splitMessage[0];
        if(first.equals("scan")) {
            //announce your server name
            client.writeMessage(announce(name));

        } else if(first.equals("connect")) {
            //save the name for this client, he is now officially connected
            String username = splitMessage[1];
            try {
                client.setName(username);
                client.writeMessage(respond(games.toArray(new Game[games.size()])));
            } catch (IllegalNameException e) {
                client.writeMessage(exception("Illegal name"));

            }

        } else if(first.equals("join")) {
            try {
                client.setPlayer();
            } catch (IllegalNameException e) {
                client.writeMessage(exception("Illegal name"));

            }
            boolean foundGame = false;
            //add the client to a game if possible, if given add him to a game with a specific max player count or specific name
            if(splitMessage.length == 2) {
                String arg = splitMessage[1];
                if(arg.length() == 1) {
                    //if a player count is given
                    char argChar = arg.charAt(0);
                    for(Game g : games) {
                        if(g.getMaxPlayers() == (int) argChar && g.hasSpace()) {
                            g.addPlayer(client.getPlayer());
                            client.setGame(g);
                            break;
                        }
                    }
                    if(foundGame) {
                        forwardToGame(join(client.getPlayer()), client);
                    } else {
                        client.writeMessage(exception("There is no game with player count: " + arg));
                    }
                    } else {
                    //if a game name is given
                    for(Game g : games) {
                        if(g.getName().equals(arg) && g.hasSpace()) {
                            g.addPlayer(client.getPlayer());
                            client.setGame(g);
                            foundGame = true;
                            break;
                        }
                    }
                    if(foundGame) {
                        forwardToGame(join(client.getPlayer()), client);
                    } else {
                        client.writeMessage(exception("There is no game with username: " + arg));
                    }
                }

            } else {
                //If the client wants to join any game
                for(Game g : games) {
                    if(g.hasSpace()) {
                        g.addPlayer(client.getPlayer());
                        client.setGame(g);
                        foundGame = true;
                        break;
                    }
                }
                if(foundGame) {
                    forwardToGame(join(client.getPlayer()), client);
                } else {
                    client.writeMessage(exception("There is no game available"));
                }
            }

        } else if(first.equals("create")) {
            //If this player wants to create a game
            int maxPlayers = Integer.parseInt(splitMessage[1]);
            try {
                client.setPlayer();
            } catch (IllegalNameException e) {
                System.out.println("[Server] Illegal name"); //should not happen
                e.printStackTrace();
            }

            if(client.getGame() != null) {
                    client.writeMessage(exception("You are already in a game!"));
                } else if(maxPlayers > 4 || maxPlayers < 2) {
                    client.writeMessage(exception("Max player count is invalid, must be between 2 and 4"));
                } else if(client.getName() == null) {
                    client.writeMessage(exception("illegal name."));
                } else {
                    Game game = new Game(maxPlayers);
                    System.out.println("added game: " + game);
                    games.add(game);
                    client.setGame(game);
                    game.addPlayer(client.getPlayer());
                    forward(respond(games.toArray(new Game[games.size()])));
                }

        } else if(first.equals("start")) {
            //if a player wants to start the game, must be the player who created it
            if(client.getGame() != null && client.getName() != null && client.getGame().getName().equals(client.getName())) {
                client.getGame().start(); //TODO start() does nothing now
                forwardToGame(turn(client.getPlayer()), client);
            } else {
                client.writeMessage(exception("You have no lobby of yourself"));
            }

        } else if(first.equals("move")) {
            //if the client makes a move

            int multiplier = Integer.parseInt(splitMessage[2]);
            Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
            Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
            Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[5]);
            Tile tile = new Tile(multiplier, c1, c2, c3);
            int index = Integer.parseInt(splitMessage[6]);

            try {
                client.getPlayer().makeMove(client.getGame().getBoard(), tile, index);
                forwardToGame(move(client.getPlayer(), tile, index), client);
            } catch (MoveException e) {
                client.writeMessage(exception("illegal move"));
            }

        } else if(first.equals("swap")) {
            boolean swap = true;

            for(Tile t : client.getPlayer().getInventory()) {
                if(client.getGame().getBoard().getPossibleFields(t) != null) {
                    client.writeMessage(exception("Cannot swap!"));
                    swap = false;
                    break;
                }
            }

            if(swap) {
                int multiplier = Integer.parseInt(splitMessage[2]);
                Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
                Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
                Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[5]);
                Tile oldTile = new Tile(multiplier, c1, c2, c3);

                Tile newTile = client.getGame().getBag().take();
                client.getPlayer().removePiece(oldTile);
                client.getPlayer().addPiece(newTile);
                forwardToGame(swap(client.getPlayer(), oldTile, newTile), client);
            }

        } else if(first.equals("skip")) {
            boolean skip = true;
            //TODO skip turn
            for(Tile t : client.getPlayer().getInventory()) {
                if(client.getGame().getBoard().getPossibleFields(t) != null) {
                    client.writeMessage(exception("Cannot skip!"));
                    skip = false;
                    break;
                }
            }

            if(skip) {
                ArrayList<Player> players = client.getGame().getPlayers();
                int playerIndex = players.indexOf(client.getPlayer());
                forwardToGame(turn(players.get(playerIndex + 1 % players.size())), client);
            }

        } else if(first.equals("leave")) {
            ArrayList<Player> players = client.getGame().getPlayers();
            players.remove(client.getPlayer());

            forwardToGame(end(players.toArray(new Player[players.size()])), client);

            Game oldGame = client.getGame();

            for(ConnectedClient c : connectedClients) {
                if(c.getGame() == oldGame) {
                    c.setGame(null);
                }
            }

        } else if(first.equals("disconnect")) {
            //disconnects the client from the server, closes the socket and removes him from

            ArrayList<Player> players = client.getGame().getPlayers();
            players.remove(client.getPlayer());

            forwardToGame(end(players.toArray(new Player[players.size()])), client);

            Game oldGame = client.getGame();

            for(ConnectedClient c : connectedClients) {
                if(c.getGame() == oldGame) {
                    c.setGame(null);
                }
            }

            client.disconnect();
            connectedClients.remove(client);

        } else if(first.equals("message")) {
            //send this message to all players in the same game
            forwardToGame(message(client.getPlayer(), splitMessage[1]), client);
        }

    }

    @Override
    public String announce(String serverName) {
        return ServerProtocol.ANNOUNCE + ";" + serverName;
    }

    @Override
    public String respond(Game... games) {
        String result = ServerProtocol.RESPOND;
        for(Game g : games) {
            result += ";" + g.getName() + ";" + g.getMaxPlayers() + ";" + g.getPlayers().size();
        }
        return result;
    }

    @Override
    public String give(Player player, Tile tile, Tile... tiles) {
        String result = ServerProtocol.GIVE + player.getName() + ";" + tile.toString();
        for (Tile p : tiles) {
            result += ";" + p.toString();
        }
        return result;
    }

    @Override
    public String turn(Player player) {
        return ServerProtocol.TURN + ";" + player.getName();
    }

    @Override
    public String move(Player player, Tile tile, int index) {
        return ServerProtocol.MOVE + ";" + player.getName() + ";" + tile.toString() + ";" + index;
    }

    @Override
    public String swap(Player player, Tile tile, Tile returnedTile) {
        return ServerProtocol.MOVE + ";" + player.getName() + ";" + tile.toString() + ";" + returnedTile.toString();
    }

    @Override
    public String skip(Player player) {
        return ServerProtocol.SKIP + ";" + player.getName();
    }

    @Override
    public String end(Player... players) {
        String result = ServerProtocol.END;
        for(Player p : players) {
            result += ";" + p.getName();
        }
        return result;
    }

    @Override
    public String exception(String message) {
        return ServerProtocol.EXCEPTION + ";" + message;
    }

    @Override
    public String message(Player player, String message) {
        System.out.println(player);
        System.out.println(message);
        System.out.println(player.toString());
        return ServerProtocol.MESSAGE + ";" + player.getName() + ";" + message;
    }

    @Override
    public String join(Player player) {
        return ServerProtocol.JOIN + ";" + player.getName();
    }

    //A class that holds information about a connected player
    public class ConnectedClient implements Runnable {
        private Socket socket;
        private BufferedReader in;
        private PrintWriter out;
        private Server server;
        private String name;
        private Game game;
        private NetworkPlayer player;

        //creates a connectedClient with a socket and a server
        //@ requires socket != null && server != null;
        //@ ensures socket != null && server != null;
        public ConnectedClient(Socket socket, Server server) {
            this.socket = socket;
            this.server = server;
            try {
                in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                out = new PrintWriter(socket.getOutputStream(), true);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        //assigns this client to a player
        //@ ensures !getName().contains(";") => player != null;
        public void setPlayer() throws IllegalNameException {
            player = new NetworkPlayer(name, this);
        }

        //gets the player object this client is assigned to
        //@ requires player != null;
        //@ pure
        public NetworkPlayer getPlayer() {
            return player;
        }

        //disconnects from the bufferedreader, the printwriter, and the socket
        //@ requires in != null && out != null && socket != null;
        public void disconnect() {
            try {
                in.close();
                out.close();
                socket.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        //assign this client to a game
        //@ requires game != null;
        //@ ensures game != null;
        public void setGame(Game game) {
            this.game = game;
        }

        //gets the game this client is in
        //@ requires game != null;
        //@ pure
        public Game getGame() {
            return game;
        }

        //gets the name of this client
        //@ requires name != null;
        //@ pure
        public String getName() {
            return name;
        }

        //set the name of this client
        //@ requires name != null;
        //@ ensures name.contains(";") => name != null;
        public void setName(String name) throws IllegalNameException {
            if(!name.contains(";") && name != null) {
                this.name = name;
            } else {
                throw new IllegalNameException("Illegal name");
            }
        }

        //read the bufferedreader
        //@ requires in != null;
        public String read() {
            try {
                String message = in.readLine();
                System.out.println("[Server] received message: " + message);
                return message;
            } catch (IOException e) {
                e.printStackTrace();
            }
            return"error";
        }

        //writes a split message
        //@ requires splitMessage != null && out != null;
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

        //writes a message
        //@ requires message != null && out != null;
        //@ pure
        public void writeMessage(String message) {
            out.println(message);
            out.flush();

        }

        //returns the reader
        //@ requires in != null;
        //@ pure
        public BufferedReader getReader() {
            return in;
        }

        //returns the writer
        //@ requires out != null;
        //@ pure
        public PrintWriter getWriter() {
            return out;
        }

        //returns the socket
        //@ requires socket != null;
        //@ pure
        public Socket getSocket() {
            return socket;
        }

        //handles a thread that is responsible for reading the reader this client is connected to
        //@ requires socket != null && server != null;
        @Override
        public void run() {
            while(socket.isConnected()) {
                String message = read();
                String[] splitMessage = message.split(";");
                server.readMessage(splitMessage, this);
            }
            disconnect();
            server.removeClient(this);
        }
    }
}
