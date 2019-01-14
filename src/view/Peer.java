package group92.spectrangle.view;

import java.io.*;
import java.net.Socket;

public class Peer {
    private BufferedReader in;
    private BufferedWriter out;
    private Socket socket;
    private String name;


    public Peer(String name, Socket socket) {
        this.name = name;
        this.socket = socket;
        try {
            in = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
            out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream(), "UTF-8"));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
