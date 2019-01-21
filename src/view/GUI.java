package group92.spectrangle.view;

import javax.swing.*;

public class GUI {

    public static void main(String[] args) {
        new GUI();
    }

    public GUI() {
        JFrame guiFrame = new JFrame();
        guiFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        guiFrame.setTitle("Spectrangle");
        guiFrame.setSize(600,500);
        guiFrame.setLocationRelativeTo(null);
        guiFrame.setVisible(true);
        JButton test = new JButton("test");
//        test.setHorizontalAlignment(0);
//        test.setVerticalAlignment(0);
//        test.setVisible(true);
    }
}
