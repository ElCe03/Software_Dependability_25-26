package test;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

import java.io.IOException;

public class MainFx extends Application {

    private static Stage primaryStage;

    @Override
    public void start(Stage stage) throws Exception {
        primaryStage = stage;
        loadPage("Login.fxml"); // Load login form first

        primaryStage.setTitle("Epic Login & Navigation");
        primaryStage.setMinWidth(800);  // Minimum window size
        primaryStage.setMinHeight(600);
        primaryStage.setMaxWidth(2000); // Optional: Max window size
        primaryStage.setMaxHeight(900);
        primaryStage.show();
    }

    public static void loadPage(String fxmlFile) {
        try {
            System.out.println("Tentative de chargement de: /" + fxmlFile);
            java.net.URL fxmlUrl = MainFx.class.getResource("/" + fxmlFile);
            System.out.println("getResource(\"/" + fxmlFile + "\") -> " + fxmlUrl);

            java.net.URL alt = MainFx.class.getResource(fxmlFile);
            System.out.println("getResource(\"" + fxmlFile + "\") -> " + alt);

            if (fxmlUrl == null && alt == null) {
                System.err.println("FXML introuvable via getResource. Classepath: " + System.getProperty("java.class.path"));
                throw new RuntimeException("FXML introuvable : /" + fxmlFile);
            }

            FXMLLoader loader = new FXMLLoader((fxmlUrl != null) ? fxmlUrl : alt);
            Parent root = loader.load();
            primaryStage.setScene(new Scene(root));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    public static void main(String[] args) {
        launch(args);
    }
}
