package group92.spectrangle.view;

import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Client;
import group92.spectrangle.network.Server;

import javax.imageio.ImageIO;
import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Observable;

public class GUI implements View {

    private static GUI GUI;

    public GUI(Client client) {
        this.client = client;
        GUI = this;
    }

    private JFrame frame;
    private Container logIn;
    private Container serverBrowser;
    private Container gameList;
    private Container gameBoard;
    private String username;
    private Server server;
    private Client client;
    private JList serverJList;
    private JList gameJList;
    private DefaultListModel<String> model;
    private String connectedServerIP;
    private String connectedServerPort;
    private String connectedServerName;

    public static void main(String[] args) {
        GUI gui = new GUI(new Client());
        gui.start();
    }

    public static GUI get() {
        return GUI;
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

        MouseListener mouseListener = new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if(e.getClickCount() == 2) {
                    String selectedValue = (String) serverJList.getSelectedValue();
                    System.out.println(selectedValue);
                    String[] splitValues = selectedValue.split("#");
                    connectedServerName = splitValues[1];
                    connectedServerIP = splitValues[3];
                    connectedServerPort = splitValues[5];
                    client.joinServer(connectedServerName, connectedServerIP, connectedServerPort);
                    gameList();
                }
            }
        };
        serverJList.addMouseListener(mouseListener);
    }

    //opens the GUI for the game list screen
    @Override
    public void gameList() {
        gameList = new GUIGameList().getPanel();
        frame.setContentPane(gameList);
        frame.revalidate();
        gameJList = (JList) gameList.getComponent(1);

        MouseListener mouseListener = new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if(e.getClickCount() == 2) {
                    String selectedValue = (String) gameJList.getSelectedValue();
                    System.out.println(selectedValue);
                    String[] splitValues = selectedValue.split("#");
                    client.join(splitValues[1]);
                    gameWindow();
                }
            }
        };
        gameJList.addMouseListener(mouseListener);

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(0)).addActionListener(e -> {
            leave();
        });

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(1)).addActionListener(e -> {
            refreshGameList();
        });

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(2)).addActionListener(e -> {
            createGame();
        });
    }

    //creates a game on the connected server
    private void createGame() {
        String[] options = { "2", "3", "4" };
        String result = (String) JOptionPane.showInputDialog(frame, "Please enter the max player amount (must be between 2-4", "Create game", JOptionPane.QUESTION_MESSAGE, null, options, options[2]);
        if (result == null) {
            System.out.println("Cancelled game creation");
        } else {
            client.create(Integer.parseInt(result));
            gameWindow();
        }
    }

    //refreshes the game list by removing all games and then sending a new connect
    //@ requires client != null && connectedServerName != null && connectedServerIP != null && connectedServerPort != null;
    private void refreshGameList() {
        ((DefaultListModel) gameJList.getModel()).removeAllElements();
        client.joinServer(connectedServerName, connectedServerIP, connectedServerPort);
    }

    //leaves a server
    private void leave() {
        client.leave();
        serverList();
    }

    //adds a game to the game list
    //@ requires name != null && maxPlayers != null && gameJList != null;
    public void addGameToList(String name, String maxPlayers, String playeramount) {
        String gameInformation = "Game name: #" + name + "# max players: #" + maxPlayers + "# current amount of players: #" + playeramount;
        ((DefaultListModel) gameJList.getModel()).addElement(gameInformation);
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
        model.addElement("Server name: #" + name + "# Server address: #" + address + "# Server port: #" + port + "#");
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

    //shows the game GUI
    @Override
    public void gameWindow() {
        gameBoard = new GUIGame().getPanel();
        JTextArea consoleArea = (JTextArea) gameBoard.getComponent(1);

        PrintStream ps = new PrintStream(new OutputStream() {
            @Override
            public void write(int b) throws IOException {
                consoleArea.append(String.valueOf((char)b));
                consoleArea.setCaretPosition(consoleArea.getDocument().getLength());
            }
        });
        System.setOut(ps);
        System.setErr(ps);

        frame.setContentPane(gameBoard);
        frame.revalidate();
        System.out.println("Opened the console on the GUI");
    }

    //creates a server
    //@ ensures !JOptionPane.showInputDialog("Please enter a server name").contains(";") => server != null;
    @Override
    public void createServer() {
        String result = JOptionPane.showInputDialog("Please enter a server name");
        if(server == null) {
            try {
                server = new Server(result);
                server.create();
            } catch (IllegalNameException e) {
                JOptionPane.showMessageDialog(frame, "Invalid server name, please do not use ';' in the server name.", "Ilegal server name", JOptionPane.ERROR_MESSAGE);
            }
        } else {
            JOptionPane.showMessageDialog(frame, "You already have a server open", "Server already open", JOptionPane.ERROR_MESSAGE);

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

    @Override
    public void update(Observable o, Object arg) {
        // TODO implement Observer here
    }

    public static class GUIBoard extends JPanel {

        private BufferedImage background;
        Path GUIPath = Paths.get("/GUI");

    //    public GUIBoard(Graphics g) {
    //        getImage();
    //        paintComponent(g);
    //    }

        public void getImage() {
            try {
                background = ImageIO.read(new File("/GUI/SpectrangleBoard"));
            } catch (IOException e) {
                System.out.println("Can't find file");
                e.printStackTrace();
            }
        }

        @Override
        protected void paintComponent(Graphics g) {
            System.out.println("test1");
            super.paintComponent(g);
            getImage();
            g.drawImage(background, 0, 0, this);
            System.out.print("test2");
        }


    }
}
