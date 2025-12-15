package controllers;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;
import java.io.IOException;
import javafx.scene.Parent;
import javafx.fxml.FXMLLoader;
import javafx.stage.Stage;

public class Interface {

    @FXML
    private VBox contentArea;  // This is where new content will appear
    @FXML
    private Button backButton;
    @FXML
    private Button    BackLogin;
    //Add this to your FXML file
    @FXML
    private void handleUsers(ActionEvent event) {
        Label userLabel = new Label("User Management Section");
        userLabel.setStyle("-fx-font-size: 18; -fx-font-weight: bold; -fx-text-fill: #2c3e50;");

        contentArea.getChildren().clear();  // Clear old content
        contentArea.getChildren().add(userLabel);  // Show new conten



        // @FXML
  // private void handleMedicalServices(ActionEvent event) {
    //    Label serviceLabel = new Label("Medical Services Section");
      //  serviceLabel.setStyle("-fx-font-size: 18; -fx-font-weight: bold; -fx-text-fill: #2c3e50;");

      //  contentArea.getChildren().clear();  // Remove old content
       // contentArea.getChildren().add(serviceLabel);  // Show new content
    //}
    try {
        // Load the Medical Services FXML
        FXMLLoader loader = new FXMLLoader(getClass().getResource("/ListeUtilisateurs.fxml"));
        Parent medicalForm = loader.load();

        contentArea.getChildren().clear();
        contentArea.getChildren().add(medicalForm);

    } catch (IOException e) {
        e.printStackTrace();
        loadContent("Error loading medical services form");
    }}
    @FXML
    private void handleEquipement (ActionEvent event) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/equipement.fxml"));
            Parent equipementView = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(equipementView);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Erreur lors du chargement de la page des équipements");
        }
    }

    @FXML
    private void handleMedicalServices(ActionEvent event) {
        try {
            // Load the Medical Services FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/medical_services.fxml"));
            Parent medicalForm = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(medicalForm);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading medical services form");
        }
    }

    private void loadContent(String text) {
        Label label = new Label(text);
        label.setStyle("-fx-font-size: 18; -fx-font-weight: bold; -fx-text-fill: #2c3e50;");
        contentArea.getChildren().clear();
        contentArea.getChildren().add(label);
    }





    @FXML
    private void handleAdminConsultation(ActionEvent event) {
        try {
            // Load the Medical Services FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/admin_consultations.fxml"));
            Parent medicalForm = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(medicalForm);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading admin consulataions view");
        }
    }



    @FXML
    private void handleMedicationStock(ActionEvent event) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/medicament.fxml"));
            Parent medicationView = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(medicationView);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading medication view");
        }
    }
    @FXML
    private void handleInfrastructure(ActionEvent event) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/departement.fxml"));
            Parent medicationView = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(medicationView);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading medication view");
        }
    }



    @FXML
    private void handlePatientDashboard(ActionEvent event) {
        try {
            // Load the Patient Dashboard in a new window
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/patient_dashboard.fxml"));
            Parent patientDashboard = loader.load();

            // Create a new stage for the dashboard
            Stage patientStage = new Stage();
            patientStage.setTitle("Patient Dashboard");
            patientStage.setScene(new Scene(patientDashboard));
            patientStage.show();
        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading patient dashboard: " + e.getMessage());
        }
    }

    @FXML
    private void handleDossiersMedicaux(ActionEvent event) {
        try {
            // Load the Dossier Medicale FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/dossier_medicale.fxml"));
            Parent dossierForm = loader.load();

            // Replace content area with the dossier medicale form
            contentArea.getChildren().clear();
            contentArea.getChildren().add(dossierForm);
        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading dossiers médicaux form: " + e.getMessage());
        }
    }
    @FXML
    private void handleSejours(ActionEvent event) {
        try {
            // Load the Sejour FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/sejour_form.fxml"));
            Parent sejourForm = loader.load();

            // Replace content area with the sejour form
            contentArea.getChildren().clear();
            contentArea.getChildren().add(sejourForm);
        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading séjours form: " + e.getMessage());
        }
    }
    @FXML
    private void handleStatistiques(ActionEvent event) {
        try {
            // Load the Statistics FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/statistiques.fxml"));
            Parent statistiquesView = loader.load();

            contentArea.getChildren().clear();
            contentArea.getChildren().add(statistiquesView);

        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading statistics view: " + e.getMessage());
        }
    }

    @FXML
    private void handleCalendar(ActionEvent event) {
        try {
            // Load the Medical Calendar FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/medical_calendar.fxml"));
            Parent calendarForm = loader.load();

            // Replace content area with the calendar form
            contentArea.getChildren().clear();
            contentArea.getChildren().add(calendarForm);
        } catch (IOException e) {
            e.printStackTrace();
            loadContent("Error loading calendar: " + e.getMessage());
        }
    }


    @FXML
    private void handleBackButton() {
        try {
            Stage stage = (Stage) backButton.getScene().getWindow();
            Parent root = FXMLLoader.load(getClass().getResource("/DashboardMedecin.fxml"));
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            showAlert("Error", "Could not load the dashboard");
        }
    }

    private void showAlert(String title, String content) {
        Alert alert = new Alert(Alert.AlertType.ERROR);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(content);
        alert.showAndWait();
    }



    @FXML
    private void handleBackLogin() {
        try {
            Stage stage = (Stage) backButton.getScene().getWindow();
            Parent root = FXMLLoader.load(getClass().getResource("/login.fxml"));
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            showAlert("Error", "Could not load the dashboard");
        }
    }
}
