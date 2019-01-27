package group92.spectrangle.view;

import java.util.Observer;

public interface View extends Observer {

    void start();

    void serverList();

    void addServer(String address, String port, String name);

    void setUsername();

    void gameWindow();

    void createServer();

    void refresh();

    void loginScreen();

}
