package group92.spectrangle;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

public class ConnectionHandler implements Runnable {
    private int amountConnected;
    private ServerSocket socket;
    private BufferedReader in;
    private BufferedWriter out;
    private Socket clientSocket;

    public ConnectionHandler(ServerSocket socket) {
        this.socket = socket;
    }

    @Override
    public void run() {
        while(amountConnected < 4) {
            try {
                clientSocket = socket.accept();
                in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream(), "UTF-8"));
                out = new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream(), "UTF-8"));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
