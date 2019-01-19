package group92.spectrangle;

import java.io.*;
import java.net.*;

import static java.lang.Thread.sleep;

public class Client implements Runnable {
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

    public void join() {
        try {
            hostAddress = InetAddress.getByName(ipv4);
            socket = new Socket(hostAddress, Game.PORT);
            out = new PrintWriter(socket.getOutputStream(), true);
            in = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
            Thread t = new Thread(this);
            t.start();
            //TODO create thread to receive messages and send messages
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

    @Override
    public void run() {
        while(socket.isConnected()) {
            String message = "";
            try {
                message = in.readLine();
                System.out.println("received message: " + message);
            } catch (IOException e) {
                e.printStackTrace();
            }
            //TODO read message and do the corresponding thing
        }
    }
}
