package group92.spectrangle;

import java.io.*;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketAddress;

public class ConnectionHandler implements Runnable {
    private ServerSocket socket;
    private BufferedReader in;
    private BufferedWriter out;
    private Socket clientSocket;
    private Server server;

    //Initializes the ConnectionHandler with a server socket and a server object
    public ConnectionHandler(ServerSocket socket, Server server) {
        this.socket = socket;
        this.server = server;
    }

    //Keeps waiting for a client to connect, when one connects it will create a writer and reader and give this to the server object
    @Override
    public void run() {
        while(true) {
            try {
                clientSocket = socket.accept();
                SocketAddress socketAddress = clientSocket.getRemoteSocketAddress();
                InetAddress address = clientSocket.getInetAddress();
                System.out.println(clientSocket.toString());
                in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream(), "UTF-8"));
                out = new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream(), "UTF-8"));
                server.addClient(in, out, clientSocket);
                //TODO create a new thread for readIn
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    //Constantly reads the buffered reader to check for incoming messages
    public void readIn(BufferedReader in, BufferedWriter out, Socket clientSocket) {
        while(clientSocket.isConnected()) {
            try {
                String message = in.readLine();
                String[] splitMessage = message.split(";");
                server.readMessage(splitMessage, out);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        server.removeClient(clientSocket);
    }
}
