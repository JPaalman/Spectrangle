package group92.spectrangle.view;

import javax.swing.*;
import java.awt.*;

public class GUInew {
    private JFrame mainFrame;
    private static final int PADDINGHORIZONTAL = 25;
    private static final int PADDINGVERTICAL = 5;


    public static void main(String[] args) {
        GUInew gui = new GUInew();
        gui.start();
    }

    //creates the main frame that holds everything
    public void start() {
//        JFrame.setDefaultLookAndFeelDecorated(true);

        mainFrame = new JFrame("Spectrangle");
        mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        Insets insets = mainFrame.getInsets();
        mainFrame.setSize(600 + insets.left + insets.right, 250 + insets.top + insets.bottom);

        loginScreen(mainFrame.getContentPane());

        mainFrame.setVisible(true);
    }

    //creates the login screen where a client has to enter his username
    public void loginScreen(Container pane) {
        pane.setLayout(null);
        JLabel usernameLable = new JLabel("Username:");
        Dimension size = usernameLable.getPreferredSize();
        Insets insets = pane.getInsets();
        usernameLable.setBounds(PADDINGHORIZONTAL + insets.left,  mainFrame.getHeight() / 3, size.width, size.height);
        pane.add(usernameLable);

        JTextField usernameField = new JTextField(10);
        size = usernameField.getPreferredSize();
        usernameField.setBounds(2*PADDINGHORIZONTAL + insets.left + usernameLable.getWidth(), mainFrame.getHeight() / 3, size.width, size.height);
        pane.add(usernameField);

        JButton usernameButton = new JButton("Confirm");
        usernameButton.addActionListener(e -> {
            System.out.println("test");
        });
        pane.add(usernameButton);
        size = usernameButton.getPreferredSize();
        usernameButton.setBounds(3*PADDINGHORIZONTAL + insets.left + usernameLable.getWidth() + usernameField.getWidth(), mainFrame.getHeight() / 3, size.width, size.height);
    }
}
