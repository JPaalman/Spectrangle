package group92.spectrangle.view;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Client;
import group92.spectrangle.network.Server;
import group92.spectrangle.players.NetworkPlayer;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.Protocol;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.ArrayList;
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
    private DefaultListModel<String> gamesModel;
    private String connectedServerIP;
    private String connectedServerPort;
    private String connectedServerName;
    private Client.ConnectedServer connectedServer;
    private int connectedGamePlayerCount;
    private JTextArea messagesArea;
    private JTextArea inputArea;
    private JTextArea inventoryArea;
    private TUI tui;

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
                    connectedServer = client.getConnectedServer(connectedServerName, connectedServerIP, connectedServerPort);
                    client.joinServer(connectedServerName, connectedServerIP, connectedServerPort);
                    gameList();
                }
            }
        };
        serverJList.addMouseListener(mouseListener);
    }

    //notify the client whose turn it is
    public void notifyTurn(String name) {
        if(name.equals(username)) {
            JOptionPane.showMessageDialog(frame, "It's your turn!");
        } else {
            JOptionPane.showMessageDialog(frame, "It's " + name + "'s turn!");
        }
    }

    //opens the GUI for the game list screen
    @Override
    public void gameList() {
        gameList = new GUIGameList().getPanel();
        frame.setContentPane(gameList);
        frame.revalidate();
        gameJList = (JList) gameList.getComponent(1);
        gamesModel = (DefaultListModel) gameJList.getModel();

        MouseListener mouseListener = new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if(e.getClickCount() == 2) {
                    String selectedValue = (String) gameJList.getSelectedValue();
                    System.out.println(selectedValue);
                    String[] splitValues = selectedValue.split("#");
                    connectedGamePlayerCount = Integer.valueOf(splitValues[3]);
                    client.setGame(connectedGamePlayerCount);
                    connectedServer.writeMessage(client.join(splitValues[1]));
                    gameWindow();
                }
            }
        };
        gameJList.addMouseListener(mouseListener);
        ((JLabel) ((JPanel) gameList.getComponent(0)).getComponent(0)).setText(username);

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(1)).addActionListener(e -> {
            leave();
        });

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(2)).addActionListener(e -> {
            refreshGameList();
        });

        ((JButton)((JPanel) gameList.getComponent(0)).getComponent(3)).addActionListener(e -> {
            createGame();
        });
    }

    //creates a game on the connected server
    private void createGame() {
        String[] options = { "2", "3", "4" };
        String result = (String) JOptionPane.showInputDialog(frame, "Please enter the max player amount (must be between 2-4", "Create game", JOptionPane.QUESTION_MESSAGE, null, options, options[2]);
        if (result == null) {
            System.out.println("[Client] Cancelled game creation");
        } else {
            connectedServer.writeMessage(client.create(Integer.parseInt(result)));
            gameWindow();
        }
    }

    //updates the inventory area to display the toString() of all players
    //@ requires players != null;
    public void updateInventory(ArrayList<Player> players) {
        inventoryArea.selectAll();
        inventoryArea.replaceSelection("");
        for(Player p : players) {
            System.out.println("appending inventoryArea");
            inventoryArea.append("\n" + p.toString());
            inventoryArea.setCaretPosition(inventoryArea.getDocument().getLength());

        }
    }

    //updates the board to include the move
    //@ requires tile != null && index != null;
    public void drawMove(Tile tile, int index) {
        tui.makeMove(tile, index);
    }

    //announces the winner(s) of the game
    //@ requires winners != null;
    public void announceWinners(String winners) {
        JOptionPane.showMessageDialog(frame, winners + " won the game!");
    }

    //notifies the user of an exception
    //@ requires message != null;
    public void exception(String message) {
        JOptionPane.showMessageDialog(frame, message, "exception", JOptionPane.ERROR_MESSAGE);
    }

    public void skipTurn(String username) {
        if(username.equals(this.username)) {
            JOptionPane.showMessageDialog(frame, "You skipped your turn!");
        } else {
            JOptionPane.showMessageDialog(frame, username + " skipped his turn");

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
        connectedServer.writeMessage(client.leave());
        frame.setContentPane(serverBrowser);
    }

    //adds a game to the game list
    //@ requires name != null && maxPlayers != null && gameJList != null;
    public void addGameToList(String name, String maxPlayers, String playeramount) {
        String gameInformation = "Game name: #" + name + "# max players: #" + maxPlayers + "# current amount of players: #" + playeramount;
        for(int i = 0; i < gamesModel.getSize(); i++) {
            if(gamesModel.contains(name)) {
                gamesModel.remove(i);
                break;
            }
        }
        gamesModel.addElement(gameInformation);

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
    //@ requires address != null && port != null && name != null;
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
    //@ requires frame != null;
    //@ ensures gameBoard != null && messagesArea != null;
    @Override
    public void gameWindow() {
        GUIGame guiGame = new GUIGame();
        gameBoard = guiGame.getPanel();
        JTextArea boardArea = guiGame.getBoardArea();
        inputArea = guiGame.getInputArea();
        JButton sendMessageButton = guiGame.getSendButton();
        JButton skipTurnButton = guiGame.getSkipTurnButton();
        JButton swapPiece = guiGame.getSwapPieceButton();
        inventoryArea = guiGame.getInventoryArea();
        messagesArea = guiGame.getMessagesArea();
        JButton forfeitButton = guiGame.getForfeitButton();
        JLabel usernameLabel = guiGame.getUsernameLabel();
        usernameLabel.setText(username);
        JButton movePieceButton = guiGame.getMovePieceButton();

        boardArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 20));
        boardArea.setEditable(false);

        messagesArea.setEditable(false);
        inventoryArea.setEditable(false);

        forfeitButton.addActionListener(e -> {
            connectedServer.writeMessage(client.leave());
            frame.setContentPane(gameList);
        });

        JPanel piecePanel = new JPanel();
        piecePanel.add(new JLabel("Piece number:"));
        JTextField pieceNumber = new JTextField(1);
        piecePanel.add(pieceNumber);
        piecePanel.add(Box.createHorizontalStrut(15));
        piecePanel.add(new JLabel("Index on board:"));
        JTextField indexOnBoard = new JTextField(2);
        piecePanel.add(indexOnBoard);


        movePieceButton.addActionListener(e -> {
            int result = JOptionPane.showConfirmDialog(frame, piecePanel, "Move piece", JOptionPane.OK_CANCEL_OPTION);
            if(result == JOptionPane.OK_OPTION) {
                int pieceNum = Integer.parseInt(pieceNumber.getText());
                int i = Integer.getInteger(indexOnBoard.getText());
                if(!Board.isLegal(i)) {
                    JOptionPane.showMessageDialog(frame, "Invalid board index", "Ilegal board index", JOptionPane.ERROR_MESSAGE);
                } else if(pieceNum > client.getGame().getPlayer(username).getInventory().size()) {
                    JOptionPane.showMessageDialog(frame, "Invalid piece number", "Ilegal piece", JOptionPane.ERROR_MESSAGE);
                } else {
                    connectedServer.writeMessage(client.move(client.getGame().getPlayer(username).getInventory().get(pieceNum - 1), i));
                }
            }
        });

        skipTurnButton.addActionListener(e -> {
            connectedServer.writeMessage(client.skip());
        });

        swapPiece.addActionListener(e -> {
            String[] options = {"1", "2", "3", "4", "5", "6"};
            String result = (String) JOptionPane.showInputDialog(frame, "Piece number:", "Swap piece", JOptionPane.QUESTION_MESSAGE, null, options, options[0]);
            int resultInt = Integer.parseInt(result);
            if(resultInt > client.getGame().getPlayer(username).getInventory().size()) {
                JOptionPane.showMessageDialog(frame, "Invalid piece number", "Ilegal piece", JOptionPane.ERROR_MESSAGE);
            } else {
                connectedServer.writeMessage(client.swap(client.getGame().getPlayer(username).getInventory().get(resultInt)));
            }
        });

        sendMessageButton.addActionListener(e -> {
            executeCommand();
        });

        //an action for when someone presses enter in the inputArea
        Action pressedEnter = new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                executeCommand();
            }
        };

        inputArea.getInputMap().put(KeyStroke.getKeyStroke("ENTER"),
                pressedEnter);

//        PrintStream ps = new PrintStream(new OutputStream() {
//            @Override
//            public void write(int b) throws IOException {
//                boardArea.append(String.valueOf((char)b));
//                boardArea.setCaretPosition(boardArea.getDocument().getLength());
//            }
//        });
//        System.setOut(ps);
//        System.setErr(ps);

        frame.setContentPane(gameBoard);
        frame.revalidate();
        System.out.println("Opened the console on the GUI");

        forfeitButton.addActionListener(e -> {
            forfeit();
        });

        client.setGame(connectedGamePlayerCount);
        client.getGame().addPlayer(client.getPlayer());
        for(int i = 1; i < connectedGamePlayerCount; i++) { //add all networkplayers to the game
            client.getGame().addPlayer(new NetworkPlayer());
        }

        tui = new TUI();
        messagesArea.append(tui.HELP);

        boardArea.append(tui.getBoard());
    }

    //executes a command
    //@ requires command != null;
    public void executeCommand() {
        String command = inputArea.getText();
        inputArea.selectAll();
        inputArea.replaceSelection("");
        System.out.println("test");
        String[] splitCommand = command.split(";");
        String firstArg = splitCommand[0];
        switch(firstArg) {
            case "help" :
                messagesArea.append("\n" + TUI.HELP);
                break;
            case Protocol.MESSAGE :
                connectedServer.writeMessage(client.message(splitCommand[1]));
                break;
            case Protocol.START :
                connectedServer.writeMessage(client.start());
                break;
            case Protocol.MOVE :
                int multiplier = Integer.parseInt(splitCommand[1]);
                Color c1 = Protocol.STRING_COLOR_MAP.get(splitCommand[2]);
                Color c2 = Protocol.STRING_COLOR_MAP.get(splitCommand[3]);
                Color c3 = Protocol.STRING_COLOR_MAP.get(splitCommand[4]);
                int index = Integer.parseInt(splitCommand[5]);
                Tile tile = new Tile(multiplier, c1, c2, c3);
                connectedServer.writeMessage(client.move(tile, index));
                break;
            case Protocol.SWAP :
                multiplier = Integer.parseInt(splitCommand[1]);
                c1 = Protocol.STRING_COLOR_MAP.get(splitCommand[2]);
                c2 = Protocol.STRING_COLOR_MAP.get(splitCommand[3]);
                c3 = Protocol.STRING_COLOR_MAP.get(splitCommand[4]);
                tile = new Tile(multiplier, c1, c2, c3);
                connectedServer.writeMessage(client.swap(tile));
                break;
            case Protocol.SKIP :
                connectedServer.writeMessage(client.skip());
            case Protocol.LEAVE :
                leave();
        }

    }

    //adds a message to the message area
    //@ requires message != null && messageArea != null;
    public void addMessage(String username, String message) {
        messagesArea.append("\n" + "[" + username + "] " + message);
        messagesArea.setCaretPosition(messagesArea.getDocument().getLength());
    }

    //Forfeit a game
    private void forfeit() {
        connectedServer.writeMessage(client.leave());
        PrintStream ps = new PrintStream(new FileOutputStream(FileDescriptor.out));
        System.setOut(ps);
        System.setOut(ps);
        System.out.println("[Client] Back to the old console");
        frame.setContentPane(gameList);
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

    public class systemOut extends PrintStream {
        private OutputStream out;
        private JTextArea textArea;

        public systemOut(OutputStream out, JTextArea textArea) {
            super(out);
            this.out = out;
            this.textArea = textArea;
        }

        @Override
        public void write(int b) {
            textArea.append(String.valueOf((char)b));
            textArea.setCaretPosition(textArea.getDocument().getLength());
            try {
                out.write(b);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
