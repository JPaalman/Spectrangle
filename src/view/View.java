package group92.spectrangle.view;

import group92.spectrangle.Game;
import javafx.stage.Stage;

public interface View {

    public void start();

    public void serverList();

    public void addServer(String address, String port, String name);

    public void setUsername();

    public void gameWindow();

    public void createServer();

    public void refresh();

    public void loginScreen();

}
