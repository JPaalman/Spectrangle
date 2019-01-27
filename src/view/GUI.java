package group92.spectrangle.view;

import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Client;
import group92.spectrangle.network.Server;
import group92.spectrangle.players.ClientPlayer;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

public class GUI implements View {
    private JFrame frame;
    private Container logIn;
    private Container serverBrowser;
    private String username;
    private Server server;
    private Client client;
    private JList serverJList;
    private DefaultListModel<String> model;

    public static void main(String[] args) {
        GUI gui = new GUI(new Client());
        gui.start();
    }

    public GUI(Client client) {
        this.client = client;
    }

    //initializes the frame and draws the login screen
    //@ ensures frame != null && frame.isVisible() == true;
    @Override
    public void start() {
        frame = new JFrame("Spectrangle");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.pack();
        frame.setSize(frame.getMaximumSize());
        loginScreen();
        frame.setVisible(true);
    }

    @Override
    //shows the server list GUI
    //@ requires frame != null;
    //@ ensures serverBrowser != null;
    public void serverList() {
        serverBrowser = new GUIServerBrowser().getMainPanel();
        frame.setContentPane(serverBrowser);
        frame.revalidate();

        serverJList = ((JList) serverBrowser.getComponent(1));
        model = (DefaultListModel) serverJList.getModel();

        ((JLabel)((JPanel) serverBrowser.getComponent(0)).getComponent(0)).setText(username);
        ((JButton)((JPanel) serverBrowser.getComponent(0)).getComponent(1)).addActionListener(e -> {
            frame.setContentPane(logIn);
        });

        ((JButton)((JPanel) serverBrowser.getComponent(0)).getComponent(2)).addActionListener(e -> {
            addServerManually();
        });

        ((JButton)((JPanel) serverBrowser.getComponent(0)).getComponent(3)).addActionListener(e -> {
            createServer();
        });

        ((JButton)((JPanel) serverBrowser.getComponent(0)).getComponent(4)).addActionListener(e -> {
            refresh();
        });
    }

    //Adds a server manually to the server list
    //@ requires frame != null;
    public void addServerManually() {
        JTextField address = new JTextField();
        address.setText("255.255.255.255");
        JTextField port = new JTextField();
        port.setText("2019");

        JPanel serverPanel = new JPanel();
        serverPanel.add(new JLabel("Address:"));
        serverPanel.add(address);
        serverPanel.add(Box.createHorizontalStrut(15));
        serverPanel.add(new JLabel("Port:"));
        serverPanel.add(port);
        int result = JOptionPane.showConfirmDialog(frame, serverPanel, "Please enter the address and the port", JOptionPane.OK_CANCEL_OPTION);
        if (result == JOptionPane.OK_OPTION) {
            System.out.println("test");
            //TODO add the server
        } else if (result == JOptionPane.CANCEL_OPTION) {

        }
    }

    //adds a server to the list of servers on the server browser and adds a mouselistener to this server
    @Override
    public void addServer(String address, String port, String name) {
        model.addElement("Server name: #" + name + "# - Server address: #" + address + "# - Server port: #" + port + "#");
        MouseListener mouseListener = new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if(e.getClickCount() == 2) {
                    String selectedValue = (String) serverJList.getSelectedValue();
                    System.out.println(selectedValue);
                    String[] splitValues = selectedValue.split("#");
                    client.joinServer(splitValues[1], splitValues[3], splitValues[5]);
                }
            }
        };
        serverJList.addMouseListener(mouseListener);
    }

    //Sets the username if it is valid
    //@ requires frame != null && logIn != null;
    //@ ensures ((JTextField) !logIn.getComponent(3)).getText().contains(";") => username != null && player != null && serverBrowser.getComponent(0)).getComponent(0)).getText().equals(username);
    @Override
    public void setUsername() {
        try {
            username = ((JTextField) logIn.getComponent(3)).getText();
            client.setName(username);
            if(serverBrowser == null) {
                serverList();
            } else {
                frame.setContentPane(serverBrowser);
                ((JLabel)((JPanel) serverBrowser.getComponent(0)).getComponent(0)).setText(username);
            }
        } catch (IllegalNameException e) {
            JOptionPane.showMessageDialog(frame, "Invalid name, please do not use ';' in your name.", "Ilegal username", JOptionPane.ERROR_MESSAGE);
        }
    }

    @Override
    public void gameWindow() {
        //TODO
    }

    //creates a server
    @Override
    public void createServer() {
        String result = JOptionPane.showInputDialog("Please enter a server name");
        try {
            server = new Server(result);
            server.create();
        } catch (IllegalNameException e) {
            e.printStackTrace();
        }
    }

    //refreshes the server list
    //@ ensures client != null;
    @Override
    public void refresh() {
        client.searchForServer();
    }

    //shows the login screen GUI
    //@ requires frame != null;
    //@ ensures logIn != null;
    @Override
    public void loginScreen() {
        logIn = new GUILogInScreen().getPanel();
        frame.setContentPane(logIn);
        ((JButton) logIn.getComponent(4)).addActionListener(e -> {
            setUsername();
        });
    }
}
