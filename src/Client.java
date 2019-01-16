package group92.spectrangle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.*;

public class Client {
    private String name;
    private Socket socket;
    private PrintWriter out;
    private BufferedReader in;
    private InetAddress hostAddress;
    private String ipv4 = "";

    public static void main(String[] args) {
        Client client = new Client("Alice");
        client.join();
    }

    public Client(String name) {
        this.name = name;
        try {
            DatagramSocket socket2;
            socket2 = new DatagramSocket();
            socket2.connect(InetAddress.getByName("8.8.8.8"), 10002);
            ipv4 = socket2.getLocalAddress().getHostAddress();
        } catch (SocketException | UnknownHostException e) {
            e.printStackTrace();
        }
    }

    public void join() {
        try {
            hostAddress = InetAddress.getByName(ipv4);
            socket = new Socket(ipv4, Game.PORT);
            out = new PrintWriter(socket.getOutputStream(), true);
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            //TODO create thread to receive messages and send messages
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
