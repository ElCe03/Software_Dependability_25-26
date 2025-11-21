package controllers;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Hyperlink;
import javafx.stage.Stage;
import javafx.event.ActionEvent;
import java.io.IOException;

public class PatientDashboardController {


    /*@ public normal_behavior
      @   requires event != null && event.getSource() instanceof Hyperlink;
      @   assignable \nothing;
      @ also
      @ public exceptional_behavior
      @   requires event != null && !(event.getSource() instanceof Hyperlink);
      @   assignable \nothing;
      @   signals (ClassCastException e) true;
      @*/

    @FXML
    private void handleLinkAction(ActionEvent event) {
        Hyperlink link = (Hyperlink) event.getSource();
        String linkText = link.getText();
        System.out.println("Navigating to: " + linkText);
        // Add navigation logic here, e.g., load new FXML or update UI
    }

    /*@ public normal_behavior
      @   requires event != null && event.getSource() instanceof Node;
      @   assignable \everything;
      @ also
      @ public exceptional_behavior
      @   requires event != null && !(event.getSource() instanceof Node);
      @   assignable \nothing;
      @   signals (ClassCastException e) true;
      @*/

    @FXML
    private void handleLogoutAction(ActionEvent event) {
        try {
            // Load the front.fxml file
            Parent frontPage = FXMLLoader.load(getClass().getResource("/front.fxml"));
            Scene frontScene = new Scene(frontPage);

            // Get the stage from the event source
            Stage stage = (Stage) ((Node) event.getSource()).getScene().getWindow();

            // Set the new scene
            stage.setScene(frontScene);
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            System.out.println("Error loading front.fxml: " + e.getMessage());
        }
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures true;
      @*/

    @FXML
    private void initialize() {
        // Initialization logic if needed, e.g., setting up dynamic data or bindings
    }

    /*@ public normal_behavior
      @   requires event != null && event.getSource() instanceof Node;
      @   assignable \everything;
      @ also
      @ public exceptional_behavior
      @   requires event != null && !(event.getSource() instanceof Node);
      @   assignable \nothing;
      @   signals (ClassCastException e) true;
      @*/

    @FXML
    private void handleSejour(ActionEvent event) {
        try {
            // Load the front.fxml file
            Parent frontPage = FXMLLoader.load(getClass().getResource("/dossier_medicale.fxml"));
            Scene frontScene = new Scene(frontPage);

            // Get the stage from the event source
            Stage stage = (Stage) ((Node) event.getSource()).getScene().getWindow();

            // Set the new scene
            stage.setScene(frontScene);
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            System.out.println("Error loading front.fxml: " + e.getMessage());
        }
    }
}