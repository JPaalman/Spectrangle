package group92.spectrangle.network;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

public class ConnectionHandler implements Runnable {
    private ServerSocket socket;
    private Socket clientSocket;
    private Server server;

    //Initializes the ConnectionHandler with a server socket and a server object
    //@ requires socket != null && server != null;
    //@ ensures this.socket == socket && this.server == server;
    public ConnectionHandler(ServerSocket socket, Server server) {
        this.socket = socket;
        this.server = server;
    }

    //Keeps waiting for a client to connect, when one connects it will create a writer and reader and give this to the server object
    //@ requires this.socket != null && this.server != null;
    @Override
    public void run() {
        while (true) {
            try {
                clientSocket = socket.accept();
                System.out.println("[Server] client connected: " + clientSocket.toString());
                server.addClient(clientSocket);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
