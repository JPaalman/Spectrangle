package group92.spectrangle.view;

import javax.imageio.ImageIO;
import javax.swing.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class GUIBoard extends JPanel {

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
