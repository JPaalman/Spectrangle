package group92.spectrangle.view;

import group92.spectrangle.Game;
import group92.spectrangle.exceptions.IllegalNameException;

import javax.swing.*;
import java.awt.*;

public class GUInew {
    private JFrame mainFrame;
    private static final int PADDINGHORIZONTAL = 25;
    private static final int PADDINGVERTICAL = 5;
    private Game game;
    private GridBagConstraints c;

    public GUInew(Game game) {
        this.game = game;
    }


    public static void main(String[] args) {
        GUInew gui = new GUInew(new Game());
        gui.start();
    }

    //creates the main frame that holds everything
    public void start() {
//        JFrame.setDefaultLookAndFeelDecorated(true);

        mainFrame = new JFrame("Spectrangle");
        mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        mainFrame.setSize(1000, 600);
        mainFrame.setLocationRelativeTo(null);

        loginScreen(mainFrame.getContentPane());

        mainFrame.setVisible(true);
    }

    //creates the login screen where a client has to enter his username
    public void loginScreen(Container pane) {
        pane.setLayout(new GridBagLayout());
        c = new GridBagConstraints();
        c.insets = new Insets(30, 30, 30, 30);
        Insets insets = pane.getInsets();

        JLabel usernameLable = new JLabel("Username:");
        Dimension size = usernameLable.getPreferredSize();
//        usernameLable.setBounds(mainFrame.getWidth() / 3,  mainFrame.getHeight() / 3, size.width, size.height);
        pane.add(usernameLable);
        usernameLable.setPreferredSize(size);

        JTextField usernameField = new JTextField(10);
        size = usernameField.getPreferredSize();
//        usernameField.setBounds(PADDINGHORIZONTAL + usernameLable.getX() + usernameLable.getWidth(), mainFrame.getHeight() / 3, size.width, size.height);
        pane.add(usernameField);
        usernameField.setPreferredSize(size);

        JButton usernameButton = new JButton("Confirm");
        pane.add(usernameButton);
        size = usernameButton.getPreferredSize();
//        usernameButton.setBounds(PADDINGHORIZONTAL + usernameField.getX() + usernameField.getWidth(), mainFrame.getHeight() / 3, size.width, size.height);
        usernameButton.setPreferredSize(size);

        usernameButton.addActionListener(e -> {
            String username = usernameField.getText();
            System.out.println(username);
            Boolean confirmed = false;
            try {
                game.createClient(username);
                confirmed = true;
            } catch (IllegalNameException e1) {
                System.out.println("Please enter a different name");
            }

            if (confirmed) {
                serverBrowser(pane);
            }
        });
    }

    public void serverBrowser(Container pane) {
        pane.removeAll();
        JMenuBar menu = new JMenuBar();

        JMenu changeUsername = new JMenu("Change username");
        JMenu addServer = new JMenu("Add server");

        menu.add(changeUsername);
        menu.add(addServer);
        pane.add(menu);

    }
}
