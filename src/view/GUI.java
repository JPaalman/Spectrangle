package group92.spectrangle.view;

import group92.spectrangle.board.Board;
import group92.spectrangle.board.Tile;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.network.Client;
import group92.spectrangle.network.Server;
import group92.spectrangle.players.ComputerPlayer;
import group92.spectrangle.players.Player;
import group92.spectrangle.protocol.Protocol;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Observable;

public class GUI implements View {

    public GUI(Client client) {
        this.client = client;
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
    private JTextArea boardArea;
    private boolean bot;
    private GUIGame guiGame;

    public boolean getBot() {
        return bot;
    }

    //initializes the frame and draws the login screen
    //@ ensures frame != null && frame.isVisible() == true && guiGame != null && inventoryArea != null && gameList != null && gameJlist != null && gamesModel != null;
    @Override
    public void start() {
        frame = new JFrame("Spectrangle");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.pack();
        frame.setSize(frame.getMaximumSize());
        guiGame = new GUIGame();
        inventoryArea = guiGame.getInventoryArea();
        gameList = new GUIGameList().getPanel();
        gameJList = (JList) gameList.getComponent(1);
        gamesModel = (DefaultListModel) gameJList.getModel();
        loginScreen();
        frame.setVisible(true);


    }

    @Override
    //shows the server list GUI
    //@ requires frame != null;
    //@ ensures serverBrowser != null && model != null && serverJList != null;
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
    //@ requires name != null && username != null && client != null && frame != null && inventoryArea != null;
    public void notifyTurn(String name) {
        if(name.equals(username) && !(client.getPlayer() instanceof ComputerPlayer)) {
            JOptionPane.showMessageDialog(frame, "It's your turn!");
        } else if(!(client.getPlayer() instanceof ComputerPlayer)) {
            JOptionPane.showMessageDialog(frame, "It's " + name + "'s turn!");
        }
        inventoryArea.append("\n\nIt's " + name + "'s turn");
    }

    //opens the GUI for the game list screen
    //@ requires frame != null && gameList != null && gameJList != null;
    @Override
    public void gameList() {
        frame.setContentPane(gameList);
        frame.revalidate();

        MouseListener mouseListener = new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if(e.getClickCount() == 2) {
                    String selectedValue = (String) gameJList.getSelectedValue();
                    String[] splitValues = selectedValue.split("#");
                    connectedGamePlayerCount = Integer.valueOf(splitValues[3]);
                    client.setGame(connectedGamePlayerCount);//TODO client receives turn before game is set
                    try {
                        Thread.sleep(10);//make sure the game is set before the server can start sending you messages
                    } catch (InterruptedException e1) {
                        e1.printStackTrace();
                    }
                    gameWindow();
                    connectedServer.writeMessage(client.join(splitValues[1]));
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
    //@ requires connectedServer != null && client != null;
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
    //@ requires players != null && inventoryArea != null;
    public void updateInventory(ArrayList<Player> players) {
        inventoryArea.selectAll();
        inventoryArea.replaceSelection("");
        for(Player p : players) {
            inventoryArea.append("\n" + p.toString());
            inventoryArea.setCaretPosition(inventoryArea.getDocument().getLength());

        }
    }

    //updates the board to include the move
    //@ requires tile != null && index != null && tui != null && boardArea != null;
    public void drawMove(Tile tile, int index) {
        tui.makeMove(tile, index);
        boardArea.selectAll();
        boardArea.replaceSelection("");
        String board = tui.getBoard();
        if (SwingUtilities.isEventDispatchThread()) {
            boardArea.append(board);
        } else {
            SwingUtilities.invokeLater(() -> boardArea.append(board));
        }
    }

    //announces the winner(s) of the game
    //@ requires winners != null && frame != null;
    public void announceWinners(String winners) {
        JOptionPane.showMessageDialog(frame, winners + " won the game!");
    }

    //notifies the user of an exception
    //@ requires message != null && frame != null;
    public void exception(String message) {
        JOptionPane.showMessageDialog(frame, message, "exception", JOptionPane.ERROR_MESSAGE);
    }

    //notifies the player if someone skipped a turn
    //@ requires username != null && this.username != null && client != null;
    public void skipTurn(String username) {
        if(username.equals(this.username) && !(client.getPlayer() instanceof ComputerPlayer)) {
            JOptionPane.showMessageDialog(frame, "You skipped your turn!");
        } else if (!(client.getPlayer() instanceof ComputerPlayer)) {
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
    //@ requires connectedServer != null && client != null && frame != null && serverBrowser != null;
    private void leave() {
        connectedServer.writeMessage(client.disconnect());
        frame.setContentPane(serverBrowser);
    }

    //adds a game to the game list
    //@ requires name != null && maxPlayers != null && gameJList != null && gamesModel != null;
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
    //@ requires frame != null && client != null;
    public void addServerManually() {
        JTextField address = new JTextField();
        address.setText(client.getIpv4());
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
            client.searchForServer(address.getText(), Integer.parseInt(port.getText()));
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
            JCheckBox botCheckBox = (JCheckBox) logIn.getComponent(5);
            bot = botCheckBox.isSelected();
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
        gameBoard = guiGame.getPanel();
        boardArea = guiGame.getBoardArea();
        inputArea = guiGame.getInputArea();
        JButton sendMessageButton = guiGame.getSendButton();
        JButton skipTurnButton = guiGame.getSkipTurnButton();
        JButton swapPiece = guiGame.getSwapPieceButton();
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
        piecePanel.add(Box.createHorizontalStrut(15));
        piecePanel.add(new JLabel("Rotation 1 or 2 (0 for default)"));
        JTextField rotationField = new JTextField(1);
        rotationField.setText("0");
        piecePanel.add(rotationField);



        movePieceButton.addActionListener(e -> {
            int result = JOptionPane.showConfirmDialog(frame, piecePanel, "Move piece", JOptionPane.OK_CANCEL_OPTION);
            if(result == JOptionPane.OK_OPTION) {
                int pieceNum = Integer.parseInt(pieceNumber.getText());
                int i = Integer.parseInt(indexOnBoard.getText());
                int rotation = Integer.parseInt(rotationField.getText());
                if(!Board.isLegal(i)) {
                    JOptionPane.showMessageDialog(frame, "Invalid board index", "Ilegal board index", JOptionPane.ERROR_MESSAGE);
                } else if(pieceNum > client.getGame().getPlayer(username).getInventory().size()) {
                    JOptionPane.showMessageDialog(frame, "Invalid piece number", "Ilegal piece", JOptionPane.ERROR_MESSAGE);
                } else {
                    Tile t = client.getGame().getPlayer(username).getInventory().get(pieceNum - 1);
                    t.rotate(rotation);
                    connectedServer.writeMessage(client.move(t, i));
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

        frame.setContentPane(gameBoard);
        frame.revalidate();

        forfeitButton.addActionListener(e -> {
            forfeit();
        });

        client.setGame(connectedGamePlayerCount);
        client.getGame().addPlayer(client.getPlayer());

        tui = new TUI();
        messagesArea.append(tui.HELP);

        boardArea.append(tui.getBoard());
    }

    public void invalidMove() {
        JOptionPane.showMessageDialog(frame, "Invalid move", "Invalid move", JOptionPane.ERROR_MESSAGE);
    }

    public void invalidSkip() {
        JOptionPane.showMessageDialog(frame, "Invalid skip", "Invalid skip", JOptionPane.ERROR_MESSAGE);

    }

    public void invalidSwap() {
        JOptionPane.showMessageDialog(frame, "Invalid skip", "Invalid skip", JOptionPane.ERROR_MESSAGE);

    }

    //executes a command
    //@ requires command != null;
    public void executeCommand() {
        String command = inputArea.getText();
        inputArea.selectAll();
        inputArea.replaceSelection("");
        String[] splitCommand = command.split(";");
        String firstArg = splitCommand[0];
        switch(firstArg) {
            case "help" :
                messagesArea.append("\n" + tui.HELP);
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
                if(client.getGame().getBoard().isValidMove(tile, index)) {
                    connectedServer.writeMessage(client.move(tile, index));
                } else {
                    invalidMove();
                }
                break;
            case Protocol.SWAP :
                multiplier = Integer.parseInt(splitCommand[1]);
                c1 = Protocol.STRING_COLOR_MAP.get(splitCommand[2]);
                c2 = Protocol.STRING_COLOR_MAP.get(splitCommand[3]);
                c3 = Protocol.STRING_COLOR_MAP.get(splitCommand[4]);
                tile = new Tile(multiplier, c1, c2, c3);
                for(Tile t : client.getPlayer().getInventory()) {
                    if(client.getGame().getBoard().getPossibleFields(t).length != 0) {
                        invalidSwap();
                    }
                }
                connectedServer.writeMessage(client.swap(tile));
                break;
            case Protocol.SKIP :
                for(Tile t : client.getPlayer().getInventory()) {
                    if(client.getGame().getBoard().getPossibleFields(t).length != 0) {
                        invalidSkip();
                    }
                }
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
        frame.setContentPane(gameList);
    }

    //creates a server
    //@ ensures !JOptionPane.showInputDialog("Please enter a server name").contains(";") => server != null;
    @Override
    public void createServer() {

        JTextField serverName = new JTextField();
        serverName.setText("DefaultServerName");
        JTextField port = new JTextField();
        port.setText("2019");

        JPanel serverPanel = new JPanel();
        serverPanel.add(new JLabel("Server name: "));
        serverPanel.add(serverName);
        serverPanel.add(Box.createHorizontalStrut(15));
        serverPanel.add(new JLabel("Port:"));
        serverPanel.add(port);
        int result = JOptionPane.showConfirmDialog(frame, serverPanel, "Create a server", JOptionPane.OK_CANCEL_OPTION);
        if (result == JOptionPane.OK_OPTION) {
            boolean success = false;
            try {
                server = new Server(serverName.getText());
                success = true;
            } catch (IllegalNameException e) {
                JOptionPane.showMessageDialog(frame, "Invalid server name", "Invalid name", JOptionPane.ERROR_MESSAGE);
            }
            try {
                if(success) {
                    server.create(Integer.parseInt(port.getText()));
                    client.searchForServer(client.getIpv4(), Integer.parseInt(port.getText()));
                }
            } catch (IOException e) {
                JOptionPane.showMessageDialog(frame, "Unable to create a server on port " + port.getText(), "IOException", JOptionPane.ERROR_MESSAGE);

            }
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
