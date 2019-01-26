package group92.spectrangle.network;

import group92.spectrangle.Game;
import group92.spectrangle.board.Piece;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.ClientProtocol;

import java.io.*;
import java.net.*;

public class Client implements Runnable, ClientProtocol {
    private String name;
    private Socket socket;
    private PrintWriter out;
    private BufferedReader in;
    private InetAddress hostAddress;
    private String ipv4 = "";

    public static void main(String[] args) {
        Client client = new Client("Alice");
        client.joinServer();
    }

    //creates a client with a name
    //@ requires name!= null;
    public Client(String name) {
        this.name = name;
        //This entire try catch block is to get the ipv4 address
        try {
            DatagramSocket socket2;
            socket2 = new DatagramSocket();
            socket2.connect(InetAddress.getByName("8.8.8.8"), 10002);
            ipv4 = socket2.getLocalAddress().getHostAddress();
        } catch (SocketException | UnknownHostException e) {
            e.printStackTrace();
        }
    }

    //creates a socket and connects to a server socket if one exists on the specified port
    public void joinServer() {
        try {
            hostAddress = InetAddress.getByName(ipv4);
            socket = new Socket(hostAddress, Game.PORT);
            out = new PrintWriter(socket.getOutputStream(), true);
            in = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
            Thread t = new Thread(this);
            t.start();
            BufferedReader terminalInput = new BufferedReader(new InputStreamReader(System.in));
            while(true) {
                String command = terminalInput.readLine().toLowerCase();
                if(command.equals("q")) {
                    break;
                }
                out.println(command);
                out.flush();
            }
            out.close();
            in.close();
            socket.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    //reads the bufferedreader of the serverSocket this client is connected to
    //@requires socket != null;
    @Override
    public void run() {
        while(socket.isConnected()) {
            String message = "";
            try {
                message = in.readLine();
                System.out.println("received message: " + message);
                String[] splitMessage = message.split(";");
                readMessage(splitMessage);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    //reads a message and executes the corresponding action
    //@ requires splitMessage != null;
    private void readMessage(String[] splitMessage) {
        if(splitMessage == null) {
            return;
        }

        String first = splitMessage[0];
        if(first.equals("announce")) {
            //give this server a name
            String serverName = splitMessage[1];
            //TODO give this server a name

        } else if(first.equals("respond")) {
            //TODO

        } else if(first.equals("give")) {
            //TODO

        } else if(first.equals("turn")) {
            //TODO

        } else if(first.equals("move")) {
            //TODO

        } else if(first.equals("swap")) {
            //TODO

        }  else if(first.equals("skip")) {
            //TODO

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
    public String move(Piece piece, int index) {
        return ClientProtocol.MOVE + ";" + piece.toString() + index;
    }

    @Override
    public String swap(Piece piece) {
        return ClientProtocol.SWAP + ";" + piece.toString();
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
}
