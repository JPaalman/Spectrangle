package group92.spectrangle.view;

import group92.spectrangle.Game;
import group92.spectrangle.network.Server;
import group92.spectrangle.exceptions.IllegalNameException;
import group92.spectrangle.players.HumanPlayer;
import group92.spectrangle.players.Player;
import javafx.application.Application;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

import java.util.Observable;
import java.util.Observer;

public class GUI extends Application implements Observer, View {

    private String username;
    private Player player;
    private Stage primaryStage;
    private StackPane root;
    private GridPane grid;
    private Server server;
    private static Game game = null;

    public static void main(String[] args) {
        launch(args);
    }

    @Override
    public void start(Stage primaryStage) {
        this.primaryStage = primaryStage;
        primaryStage.setTitle("Spectrangle");
        root = new StackPane();

        loginScreen();

        primaryStage.setScene(new Scene(root, 300, 250));
        primaryStage.show();
    }

    public void loginScreen() {
        grid = new GridPane();
        grid.setAlignment(Pos.CENTER);
        grid.setHgap(10);
        grid.setVgap(10);
        grid.setPadding(new Insets(25, 25, 25, 25));

        root.getChildren().add(grid);

        Label usernameLabel = new Label("Username:");
        grid.add(usernameLabel, 0, 1);

        TextField userTextField = new TextField();
        grid.add(userTextField, 1, 1);

        Button confirmUsername = new Button("Confirm");
        grid.add(confirmUsername, 0, 2);
        confirmUsername.setOnAction(event -> {
            username = userTextField.getText();
            game.createClient(username);
            serverList();
        });
    }

    public void serverList() {
        grid.getChildren().clear();

        Label serverTitle = new Label("Servers:");
        grid.add(serverTitle, 0, 0);

        if(server == null) {
            Button addServerButton = new Button("Create server");
            addServerButton.setOnAction(event -> {
                addServer();
            });

            grid.add(addServerButton, 1, 0);
        }

        //TODO list all servers
        //TODO option to manually insert port and address
    }

    public void addServer() {
        GridPane serverNameGrid = new GridPane();
        System.out.println("Creating server");
        root.getChildren().clear();

        Label serverName = new Label("Server name:");
        serverNameGrid.add(serverName, 0, 0);

        TextField serverNameField = new TextField();
        serverNameGrid.add(serverNameField, 1, 0);

        Button addServer = new Button("Add");
        addServer.setOnAction(event -> {
            try {
                server = new Server(serverNameField.getText());
                System.out.println(server.toString());
                root.getChildren().clear();
                root.getChildren().add(grid);
                serverList();

            } catch (IllegalNameException e) {
                System.out.println("Please enter a different server name");
            }
        });
        serverNameGrid.add(addServer, 1, 1);

        root.getChildren().add(serverNameGrid);
    }

    @Override
    public void update(Observable o, Object arg) {

    }
}
