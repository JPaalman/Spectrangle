package group92.spectrangle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;

public class Client {
    private String name;
    private Socket socket;
    private PrintWriter out;
    private BufferedReader in;
    private String address;
    private InetAddress hostAddress;

    public static void main(String[] args) {
        Client client = new Client("Alice", "192.168.2.4");
        client.join();
    }

    public Client(String name, String address) {
        this.name = name;
        this.address = address;
    }

    public void join() {
        try {
            hostAddress = InetAddress.getByName(address);
            socket = new Socket(address, Game.PORT);
            out = new PrintWriter(socket.getOutputStream(), true);
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            //TODO create thread to receive messages and send messages
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
