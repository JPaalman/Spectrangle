package group92.spectrangle.network;

import group92.spectrangle.Game;
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

import static java.lang.Thread.sleep;

public class Server implements ServerProtocol {
    private String name;
    private ServerSocket socket;
    private ArrayList<ConnectedClient> connectedClients;
    private ArrayList<Game> games;
    public final static int PORT = 2019;

    //starts this program from the server-side with predefined address, port, and name
    public static void main(String[] args) {
        try {
            Server server = new Server("RemiAndJaïr'sServer");
            server.create();
        } catch (IllegalNameException e) {
            System.out.println("Illegal server name");
        }
    }

    //Constructor, initializes name and gets the ipv4 address
    //@ requires name != null;
    //@ ensures !name.contains(";") && name.length() > 2 => this.name == name;
    //@ ensures connectedClients != null && games != null;
    public Server(String name) throws IllegalNameException {
        if (!name.contains(";") && name.length() > 2) {
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
        for (ConnectedClient client : connectedClients) {
            client.writeMessage(message);
        }
    }

    //sends a message to all connected clients in a game
    public void forwardToGame(String message, ConnectedClient client) {
        for (ConnectedClient c : connectedClients) {
            if (client.getGame() == c.getGame()) {
                c.writeMessage(message);
            }
        }
    }

    //Creates the server
    public void create() {
        try {
            socket = new ServerSocket(PORT);
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
        for (ConnectedClient client : connectedClients) {
            if (client.getSocket() == clientSocket) {
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
        for (ConnectedClient c : connectedClients) {
            if (client == c) {
                connectedClients.remove(client);
            }
        }
    }

    public void readMessage(String[] splitMessage, ConnectedClient client) {
        if (splitMessage == null || client == null) {
            return;
        }
        Game clientGame = client.getGame();
        NetworkPlayer clientPlayer = client.getPlayer();

        String first = splitMessage[0];

        outerLoop:
        switch (first) {
            case "scan":
                //announce your server name
                client.writeMessage(announce(name));

                break;
            case "connect":
                //save the name for this client, he is now officially connected
                String username = splitMessage[1];
                try {
                    client.setName(username);
                    client.setLobby(true);
                    client.writeMessage(respond(games.toArray(new Game[games.size()])));
                } catch (IllegalNameException e) {
                    client.writeMessage(exception("Illegal name"));

                }

                break;
            case "join":
                try {
                    client.setPlayer();
                    clientPlayer = client.getPlayer();
                } catch (IllegalNameException e) {
                    client.writeMessage(exception("Illegal name"));

                }
                boolean foundGame = false;
                //add the client to a game if possible, if given add him to a game with a specific max player count or specific name
                if (splitMessage.length == 2) {
                    String arg = splitMessage[1];
                    if (arg.length() == 1) {
                        //if a player count is given
                        char argChar = arg.charAt(0);
                        for (Game g : games) {
                            if (g.getMaxPlayers() == (int) argChar && g.hasSpace()) {
                                g.addPlayer(clientPlayer);
                                client.setGame(g);
                                client.setLobby(false);
                                foundGame = true;
                                break;
                            }
                        }
                        if (foundGame) {
                            forwardToGame(join(clientPlayer), client);
                            clientGame = client.getGame();
                            if (clientGame.getPlayers().size() == clientGame.getMaxPlayers()) { //when the last player joins
                                startGame(client);
                            }
                        } else {
                            client.writeMessage(exception("There is no game with player count: " + arg));
                        }

                    } else {
                        //if a game name is given
                        for (Game g : games) {
                            if (g.getName().equals(arg) && g.hasSpace()) {
                                g.addPlayer(clientPlayer);
                                client.setGame(g);
                                client.setLobby(false);
                                foundGame = true;
                                break;
                            }
                        }
                        if (foundGame) {
                            forwardToGame(join(clientPlayer), client);
                            clientGame = client.getGame();
                            if (clientGame.getPlayers().size() == clientGame.getMaxPlayers()) { //when the last player joins
                                startGame(client);
                            }
                        } else {
                            client.writeMessage(exception("There is no game with username: " + arg));
                        }
                    }

                } else {
                    //If the client wants to join any game
                    for (Game g : games) {
                        if (g.hasSpace()) {
                            g.addPlayer(clientPlayer);
                            client.setGame(g);
                            client.setLobby(false);
                            foundGame = true;
                            break;
                        }
                    }
                    if (foundGame) {
                        forwardToGame(join(clientPlayer), client);
                        clientGame = client.getGame();
                        if (clientGame.getPlayers().size() == clientGame.getMaxPlayers()) { //when the last player joins
                            startGame(client);
                        }
                    } else {
                        client.writeMessage(exception("There is no game available"));
                    }
                }

                break;
            case "create":
                //If this player wants to create a game
                int maxPlayers = Integer.parseInt(splitMessage[1]);
                try {
                    client.setPlayer();
                    clientPlayer = client.getPlayer();
                } catch (IllegalNameException e) {
                    System.out.println("[Server] Illegal name"); //should not happen
                    e.printStackTrace();
                }

                if (clientGame != null) {
                    client.writeMessage(exception("You are already in a game!"));
                } else if (maxPlayers > 4 || maxPlayers < 2) {
                    client.writeMessage(exception("Max player count is invalid, must be between 2 and 4"));
                } else if (client.getName() == null) {
                    client.writeMessage(exception("illegal name."));
                } else {
                    client.setLobby(false);
                    Game game = new Game(maxPlayers);
                    games.add(game);
                    client.setGame(game);
                    game.addPlayer(clientPlayer);
                    for(ConnectedClient c : connectedClients) {
                        if(c.getLobby()) {//send updated games list to all players in the lobby
                            forward(respond(games.toArray(new Game[games.size()])));
                        }
                    }
                }

                break;
            case "start":
                if (clientGame.getStarted()) {
                    client.writeMessage(exception("This game has already started"));
                } else {
                    //if a player wants to start the game, must be the player who created it
                    if (clientGame != null && client.getName() != null && clientGame.getName().equals(client.getName())) {
                        startGame(client);
                    } else {
                        client.writeMessage(exception("You have no lobby of yourself"));
                    }
                }

                break;
            case "move":
                //if the client makes a move
                if(!clientGame.getStarted()) {//if the game hasn't started yet
                    forwardToGame(exception("This game has not yet started"), client);
                    break;
                }
                if (clientGame.turn() == clientPlayer) {
                    int multiplier = Integer.parseInt(splitMessage[1]);
                    Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[2]);
                    Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
                    Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
                    Tile tile = new Tile(multiplier, c1, c2, c3);

                    if(!clientPlayer.getInventory().contains(tile)) {//if he does not have the piece
                        client.writeMessage(exception("You do not have this piece"));
                        break;
                    }

                    int index = Integer.parseInt(splitMessage[5]);
                    Tile newTile = clientGame.getBag().take();
                    try {
                        if (clientGame.getBoard().isValidMove(tile, index)) {
                            clientPlayer.makeMove(clientGame.getBoard(), tile, index);
                            forwardToGame(move(clientPlayer, tile, index), client);
                        } else {
                            client.writeMessage(exception("Invalid move :("));
                            break;
                        }

                        if (newTile != null) { //give a new piece if the bag isn't empty
                            forwardToGame(give(clientPlayer, newTile), client);
                            clientPlayer.addPiece(newTile);
                        }
                        clientGame.incrementTurn();
                        forwardToGame(turn(clientGame.turn()), client);
                    } catch (MoveException e) {
                        client.writeMessage(exception("illegal move"));
                        break;
                    }
                } else {
                    client.writeMessage(exception("It is not your turn!"));
                }

                break;
            case "swap":
                if(!clientGame.getStarted()) {//if the game hasn't started yet
                    forwardToGame(exception("This game has not yet started"), client);
                    break;
                }

                if (clientGame.turn() == clientPlayer) {
                    boolean swap = true;

                    for (Tile t : clientPlayer.getInventory()) {
                        if (clientGame.getBoard().getPossibleFields(t).length != 0) {
                            client.writeMessage(exception("Cannot swap!"));
                            swap = false;
                            break;
                        }
                    }

                    if (swap) {
                        int multiplier = Integer.parseInt(splitMessage[1]);
                        Color c1 = Protocol.STRING_COLOR_MAP.get(splitMessage[2]);
                        Color c2 = Protocol.STRING_COLOR_MAP.get(splitMessage[3]);
                        Color c3 = Protocol.STRING_COLOR_MAP.get(splitMessage[4]);
                        Tile oldTile = new Tile(multiplier, c1, c2, c3);

                        if(!clientPlayer.getInventory().contains(oldTile)) {//if he does not have the piece
                            client.writeMessage(exception("You do not have this piece"));
                            break;
                        }

                        if(clientGame.getBag().isEmpty()) {
                            client.writeMessage(exception("Cannot swap the bag is empty"));
                            break;
                        }

                        Tile newTile = clientGame.getBag().take();
                        clientPlayer.swap(newTile, oldTile);
                        clientGame.getBag().put(oldTile);
                        forwardToGame(swap(clientPlayer, oldTile, newTile), client);
                        clientGame.incrementTurn();
                        forwardToGame(turn(clientGame.turn()), client);
                    }
                } else {
                    client.writeMessage(exception("It is not your turn!"));
                }

                break;
            case "skip":
                if(!clientGame.getStarted()) {//if the game hasn't started yet
                    client.writeMessage(exception("This game has not yet started"));
                    break;
                }

                if (clientGame.turn() == clientPlayer) {
                    boolean skip = true;
                    for (Tile t : clientPlayer.getInventory()) {
                        for (int i = 0; i < 3; i++) {
                            if (clientGame.getBoard().getPossibleFields(t).length != 0) {
                                client.writeMessage(exception("Cannot skip!"));
                                skip = false;
                                break;
                            }
                            t.rotate(1);
                        }
                    }

                    if (skip) {
                        if(clientGame.getBag().isEmpty()) {//if the bag is empty and no players can make a move the game is over
                            for(Player p : clientGame.getPlayers()) {
                                if(!(p == clientPlayer)) {//we already checked the clientPlayer himself
                                    for(Tile t : p.getInventory()) {
                                        if(clientGame.getBoard().getPossibleFields(t).length != 0) {//if there is a possible move left, continue
                                            forwardToGame(skip(clientPlayer), client);
                                            clientGame.incrementTurn();
                                            forwardToGame(turn(clientGame.turn()), client);
                                            break outerLoop;
                                        }
                                    }

                                    for(Tile t : clientGame.getBag().getTiles()) {
                                        if(clientGame.getBoard().getPossibleFields(t).length != 0) {
                                            forwardToGame(skip(clientPlayer), client);
                                            clientGame.incrementTurn();
                                            forwardToGame(turn(clientGame.turn()), client);
                                            break outerLoop;
                                        }
                                    }

                                    //if you get here the game is over
                                    int highestScore = 0;
                                    ArrayList<Player> winners = new ArrayList<>();
                                    for(Player possibleWinner : clientGame.getPlayers()) {
                                        if(possibleWinner.getScore() > highestScore) {
                                            winners.clear();
                                            winners.add(possibleWinner);
                                        } else if(possibleWinner.getScore() == highestScore) {
                                            winners.add(possibleWinner);
                                        }
                                    }
                                    forwardToGame(end(winners.toArray(new Player[winners.size()])), client);
                                }
                            }
                        }

                    }
                } else {
                    client.writeMessage(exception("It is not your turn!"));
                }

                break;
            case "leave": {
                removePlayerFromGame(client);
                client.setLobby(false);
                break;
            }
            case "disconnect": {
                //disconnects the client from the server, closes the socket and removes him from the game he is in
                removePlayerFromGame(client);

                client.disconnect();
                connectedClients.remove(client);

                break;
            }
            case "message":
                //send this message to all players in the same game
                forwardToGame(message(clientPlayer, splitMessage[1]), client);
                break;
        }

    }

    public void removePlayerFromGame(ConnectedClient client) {
        Game clientGame = client.getGame();
        Player clientPlayer = client.getPlayer();
        if(!clientGame.getStarted()) {//if the game hasn't started yet
            forwardToGame(leave(clientPlayer), client);
            clientGame.removePlayer(clientPlayer);
        } else {
            ArrayList<Player> players = clientGame.getPlayers();
            players.remove(clientPlayer);

            forwardToGame(end(players.toArray(new Player[players.size()])), client);

            Game oldGame = clientGame;

            for (ConnectedClient c : connectedClients) {
                if (c.getGame() == oldGame) {
                    c.setGame(null);
                }
            }
        }
    }

    public String leave(Player player) {
        return Protocol.LEAVE + ";" + player.getName();
    }

    public void startGame(ConnectedClient client) {
        Game clientGame = client.getGame();
        clientGame.start();
        int i = 0;
        while (i != 4) {//notify the players of their pieces in order that they have been drawn
            for (Player p : clientGame.getPlayers()) {
                forwardToGame(give(p, p.getInventory().get(i)), client);
            }
            i++;
        }
        forwardToGame(turn(clientGame.turn()), client);
    }

    @Override
    public String announce(String serverName) {
        return ServerProtocol.ANNOUNCE + ";" + serverName;
    }

    @Override
    public String respond(Game... games) {
        String result = ServerProtocol.RESPOND;
        for (Game g : games) {
            result += ";" + g.getName() + ";" + g.getMaxPlayers() + ";" + g.getPlayers().size();
        }
        return result;
    }

    @Override
    public String give(Player player, Tile tile, Tile... tiles) {
        String result = ServerProtocol.GIVE + ";" + player.getName() + ";" + tile.toString();
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
        return ServerProtocol.SWAP + ";" + player.getName() + ";" + tile.toString() + ";" + returnedTile.toString();
    }

    @Override
    public String skip(Player player) {
        return ServerProtocol.SKIP + ";" + player.getName();
    }

    @Override
    public String end(Player... players) {
        String result = ServerProtocol.END;
        for (Player p : players) {
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
        private boolean lobby = false;

        public void setLobby(boolean lobby) {
            this.lobby = lobby;
        }

        public boolean getLobby() {
            return lobby;

        }

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
            player = new NetworkPlayer(name);
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
                System.out.println("socket already closed");
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
            if (!name.contains(";") && name != null) {
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
                System.out.println("reader closed");
                disconnect();
            }
            return "error";
        }

        //writes a split message
        //@ requires splitMessage != null && out != null;
        public void writeSplitMessage(String[] splitMessage) {
            String message = "";
            for (int i = 0; i < splitMessage.length; i++) {
                if (i == splitMessage.length - 1) {
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
            while (!socket.isClosed()) {
                String message = read();
                String[] splitMessage = message.split(";");
                server.readMessage(splitMessage, this);
            }
            disconnect();
            server.removeClient(this);
        }
    }
}
