package controllers;

import com.fasterxml.jackson.core.JsonProcessingException;
import entite.*;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.stage.Stage;
import javafx.collections.FXCollections;
import service.EmailSender;
import service.UserService;


import java.io.IOException;
import java.net.URL;
import java.sql.SQLException;
import java.util.ResourceBundle;
import java.util.regex.Pattern;

public class AjouterUtilisateurController implements Initializable {

    @FXML private TextField emailField;

    @FXML private PasswordField passwordField;

    @FXML private TextField nomField;

    @FXML private TextField prenomField;

    @FXML private ComboBox<String> typeComboBox;

    @FXML private Button btnCreer;

    @FXML private Label emailError;

    @FXML private Label passwordError;

    @FXML private Label nomError;

    @FXML private Label prenomError;

    @FXML private Label typeError;

    private final UserService userService = new UserService();

    private static final String EMAIL_REGEX = "^[A-Za-z0-9+_.-]+@[A-Za-z0-9.-]+$";

    private static final Pattern EMAIL_PATTERN = Pattern.compile(EMAIL_REGEX);

    private static final String NAME_REGEX = "^[A-Za-zÀ-ÿ\\s-]+$";

    private static final Pattern NAME_PATTERN = Pattern.compile(NAME_REGEX);

    /*@ public invariant userService != null;
      @ public invariant EMAIL_REGEX != null;
      @ public invariant EMAIL_PATTERN != null;
      @ public invariant NAME_REGEX != null;
      @ public invariant NAME_PATTERN != null;
      @*/

    /*@
      @ ensures typeComboBox.getItems().size() == 5;
      @ ensures typeComboBox.getItems().contains("medecin");
      @ ensures typeComboBox.getItems().contains("patient");
      @ ensures typeComboBox.getItems().contains("pharmacien");
      @ ensures typeComboBox.getItems().contains("staff");
      @ ensures typeComboBox.getItems().contains("admin");
      @ assignable typeComboBox.items, typeComboBox.promptText,
      @            emailError.*, passwordError.*, nomError.*, prenomError.*, typeError.*;
      @*/
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        //@ assert typeComboBox != null;

        // Initialiser le ComboBox avec les types d'utilisateurs
        typeComboBox.setItems(FXCollections.observableArrayList(
                "medecin",
                "patient",
                "pharmacien",
                "staff",
                "admin"
        ));

        //@ assert typeComboBox.getItems() != null;
        //@ assert typeComboBox.getItems().size() == 5;

        typeComboBox.setPromptText("Sélectionnez un type");

        // Réinitialiser les messages d'erreur
        resetErrorLabels();
    }

    /*@
      @ requires emailField != null;
      @ requires passwordField != null;
      @ requires nomField != null;
      @ requires prenomField != null;
      @ requires typeComboBox != null;
      @ requires userService != null;
      @ requires btnCreer != null;
      @ assignable emailError.*, passwordError.*, nomError.*, prenomError.*, typeError.*,
      @            userService.*, btnCreer.scene.window.*;
      @*/
    @FXML
    private void handleAjouterUtilisateur() {
        try {
            //@ assert emailField != null;
            //@ assert passwordField != null;
            //@ assert nomField != null;
            //@ assert prenomField != null;
            //@ assert typeComboBox != null;

            // Réinitialiser les messages d'erreur
            resetErrorLabels();

            // Récupérer les entrées
            String email = emailField.getText().trim();
            String password = passwordField.getText();
            String nom = nomField.getText().trim();
            String prenom = prenomField.getText().trim();
            String type = typeComboBox.getValue();

            //@ assert email != null;
            //@ assert password != null;
            //@ assert nom != null;
            //@ assert prenom != null;

            // Valider les entrées
            boolean isValid = true;

            // Validation du type
            if (type == null) {
                //@ assert typeError != null;
                typeError.setText("Veuillez sélectionner un type d'utilisateur.");
                typeError.setVisible(true);
                isValid = false;
            }

            // Validation de l'email
            if (email.isEmpty()) {
                //@ assert emailError != null;
                emailError.setText("L'email est requis.");
                emailError.setVisible(true);
                isValid = false;
            } else if (!EMAIL_PATTERN.matcher(email).matches()) {
                //@ assert emailError != null;
                //@ assert EMAIL_PATTERN != null;
                emailError.setText("Veuillez entrer un email valide.");
                emailError.setVisible(true);
                isValid = false;
            }

            // Validation du mot de passe
            if (password.isEmpty()) {
                //@ assert passwordError != null;
                passwordError.setText("Le mot de passe est requis.");
                passwordError.setVisible(true);
                isValid = false;
            } else if (password.length() < 8) {
                //@ assert passwordError != null;
                //@ assert password.length() < 8;
                passwordError.setText("Le mot de passe doit contenir au moins 8 caractères.");
                passwordError.setVisible(true);
                isValid = false;
            }

            // Validation du nom
            if (nom.isEmpty()) {
                //@ assert nomError != null;
                nomError.setText("Le nom est requis.");
                nomError.setVisible(true);
                isValid = false;
            } else if (!NAME_PATTERN.matcher(nom).matches()) {
                //@ assert nomError != null;
                //@ assert NAME_PATTERN != null;
                nomError.setText("Le nom ne doit contenir que des lettres et des espaces.");
                nomError.setVisible(true);
                isValid = false;
            }

            // Validation du prénom
            if (prenom.isEmpty()) {
                //@ assert prenomError != null;
                prenomError.setText("Le prénom est requis.");
                prenomError.setVisible(true);
                isValid = false;
            } else if (!NAME_PATTERN.matcher(prenom).matches()) {
                //@ assert prenomError != null;
                //@ assert NAME_PATTERN != null;
                prenomError.setText("Le prénom ne doit contenir que des lettres et des espaces.");
                prenomError.setVisible(true);
                isValid = false;
            }

            // Si une validation échoue, arrêter le traitement
            if (!isValid) {
                return;
            }

            //@ assert isValid == true;
            //@ assert !email.isEmpty();
            //@ assert !password.isEmpty();
            //@ assert password.length() >= 8;
            //@ assert !nom.isEmpty();
            //@ assert !prenom.isEmpty();
            //@ assert type != null;

            // Instancier la sous-classe appropriée
            Users user;
            switch (type.toLowerCase()) {
                case "patient":
                    user = new Patient();
                    //@ assert user instanceof Patient;
                    break;
                case "medecin":
                    user = new Medecin();
                    //@ assert user instanceof Medecin;
                    break;
                case "pharmacien":
                    user = new Pharmacien();
                    //@ assert user instanceof Pharmacien;
                    break;
                case "staff":
                    user = new Staff();
                    //@ assert user instanceof Staff;
                    break;
                case "admin":
                    user = new Users();
                    break;
                default:
                    user = new Users();
                    break;
            }

            //@ assert user != null;

            // Remplir les champs communs
            user.setEmail(email);
            user.setPassword(password);
            user.setNom(nom);
            user.setPrenom(prenom);
            user.setType(type);

            //@ assert user.getEmail() == email;
            //@ assert user.getPassword() == password;
            //@ assert user.getNom() == nom;
            //@ assert user.getPrenom() == prenom;
            //@ assert user.getType() == type;

            EmailSender.envoyerEmailInscription(email, nom, password, type);

            // Si le type est "admin", enregistrer directement et rediriger
            if (type.toLowerCase().equals("admin")) {
                //@ assert type.toLowerCase().equals("admin");

                userService.ajouterUtilisateur(user, type);
                showAlert(Alert.AlertType.INFORMATION, "Succès", "Admin créé avec succès !");

                // Redirection vers la liste des utilisateurs
                FXMLLoader loader = new FXMLLoader(getClass().getResource("/ListeUtilisateurs.fxml"));
                //@ assert loader != null;

                Parent root = loader.load();
                //@ assert root != null;

                Stage stage = (Stage) btnCreer.getScene().getWindow();
                //@ assert stage != null;

                stage.setScene(new Scene(root));
                stage.setTitle("Liste Utilisateurs");
                stage.show();
            } else {
                //@ assert !type.toLowerCase().equals("admin");

                // Redirection vers l'interface appropriée pour les autres types
                String fxmlFile;
                String title;

                switch (type.toLowerCase()) {
                    case "medecin":
                        fxmlFile = "/ajouterMedecin.fxml";
                        title = "Ajout Médecin";
                        break;
                    case "patient":
                        fxmlFile = "/ajouterPatient.fxml";
                        title = "Ajout Patient";
                        break;
                    case "pharmacien":
                        fxmlFile = "/ajouterPharmacien.fxml";
                        title = "Ajout Pharmacien";
                        break;
                    case "staff":
                        fxmlFile = "/ajouterStaff.fxml";
                        title = "Ajout Staff";
                        break;
                    default:
                        fxmlFile = "/ListeUtilisateurs.fxml";
                        title = "Liste Utilisateurs";
                        break;
                }

                //@ assert fxmlFile != null;
                //@ assert title != null;

                FXMLLoader loader = new FXMLLoader(getClass().getResource(fxmlFile));
                //@ assert loader != null;

                Parent root = loader.load();
                //@ assert root != null;

                // Passer l'utilisateur au contrôleur
                Object controller = loader.getController();
                //@ assert controller != null;

                if (controller instanceof MedecinController) {
                    //@ assert user instanceof Medecin;
                    ((MedecinController) controller).setUtilisateur((Medecin) user);
                } else if (controller instanceof PatientController) {
                    //@ assert user instanceof Patient;
                    ((PatientController) controller).setUtilisateur((Patient) user);
                } else if (controller instanceof PharmacienController) {
                    //@ assert user instanceof Pharmacien;
                    ((PharmacienController) controller).setUtilisateur((Pharmacien) user);
                } else if (controller instanceof StaffController) {
                    //@ assert user instanceof Staff;
                    ((StaffController) controller).setUtilisateur((Staff) user);
                }

                Stage stage = (Stage) btnCreer.getScene().getWindow();
                //@ assert stage != null;

                stage.setScene(new Scene(root));
                stage.setTitle(title);
                stage.show();
            }

        } catch (IllegalArgumentException e) {
            //@ assert e != null;
            showAlert(Alert.AlertType.WARNING, "Champs manquants", e.getMessage());
        } catch (IOException e) {
            //@ assert e != null;
            showAlert(Alert.AlertType.ERROR, "Erreur FXML", "Erreur lors du chargement de l'interface : " + e.getMessage());
        } catch (SQLException e) {
            //@ assert e != null;
            showAlert(Alert.AlertType.ERROR, "Erreur", "Erreur lors de la création de l'utilisateur : " + e.getMessage());
        }
    }

    /*@
      @ requires emailError != null;
      @ requires passwordError != null;
      @ requires nomError != null;
      @ requires prenomError != null;
      @ requires typeError != null;
      @ ensures emailError.getText().equals("");
      @ ensures !emailError.isVisible();
      @ ensures passwordError.getText().equals("");
      @ ensures !passwordError.isVisible();
      @ ensures nomError.getText().equals("");
      @ ensures !nomError.isVisible();
      @ ensures prenomError.getText().equals("");
      @ ensures !prenomError.isVisible();
      @ ensures typeError.getText().equals("");
      @ ensures !typeError.isVisible();
      @ assignable emailError.text, emailError.visible,
      @            passwordError.text, passwordError.visible,
      @            nomError.text, nomError.visible,
      @            prenomError.text, prenomError.visible,
      @            typeError.text, typeError.visible;
      @*/
    private void resetErrorLabels() {
        //@ assert emailError != null;
        //@ assert passwordError != null;
        //@ assert nomError != null;
        //@ assert prenomError != null;
        //@ assert typeError != null;

        emailError.setText("");
        emailError.setVisible(false);
        passwordError.setText("");
        passwordError.setVisible(false);
        nomError.setText("");
        nomError.setVisible(false);
        prenomError.setText("");
        prenomError.setVisible(false);
        typeError.setText("");
        typeError.setVisible(false);

        //@ assert emailError.getText().equals("");
        //@ assert !emailError.isVisible();
        //@ assert passwordError.getText().equals("");
        //@ assert !passwordError.isVisible();
        //@ assert nomError.getText().equals("");
        //@ assert !nomError.isVisible();
        //@ assert prenomError.getText().equals("");
        //@ assert !prenomError.isVisible();
        //@ assert typeError.getText().equals("");
        //@ assert !typeError.isVisible();
    }

    /*@
      @ requires type != null;
      @ requires title != null;
      @ requires content != null;
      @ requires !title.isEmpty();
      @ requires !content.isEmpty();
      @*/
    private void showAlert(Alert.AlertType type, String title, String content) {
        //@ assert type != null;
        //@ assert title != null && !title.isEmpty();
        //@ assert content != null && !content.isEmpty();

        Alert alert = new Alert(type);
        //@ assert alert != null;

        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(content);
        alert.showAndWait();
    }

    /*@
      @ requires event != null;
      @ requires event.getSource() != null;
      @ requires ((Node) event.getSource()).getScene() != null;
      @ requires ((Node) event.getSource()).getScene().getWindow() != null;*/
    @FXML
    private void handleBack(ActionEvent event) {
        //@ assert event != null;
        //@ assert event.getSource() != null;

        try {
            // Load the login.fxml file
            Parent LoginRoot = FXMLLoader.load(getClass().getResource("/login.fxml"));
            //@ assert LoginRoot != null;

            // Get the current stage
            Stage stage = (Stage) ((Node) event.getSource()).getScene().getWindow();
            //@ assert stage != null;

            // Set the new scene
            Scene scene = new Scene(LoginRoot);
            //@ assert scene != null;

            stage.setScene(scene);
            stage.show();
        } catch (IOException e) {
            //@ assert e != null;
            e.printStackTrace();
            showErrorAlert("Failed to load consultation page", "Please try again later.");
        }
    }

    /*@
      @ requires header != null;
      @ requires content != null;
      @ requires !header.isEmpty();
      @ requires !content.isEmpty();
      @*/
    private void showErrorAlert(String header, String content) {
        //@ assert header != null && !header.isEmpty();
        //@ assert content != null && !content.isEmpty();

        Alert alert = new Alert(Alert.AlertType.ERROR);
        //@ assert alert != null;

        alert.setTitle("Navigation Error");
        alert.setHeaderText(header);
        alert.setContentText(content);
        alert.showAndWait();
    }
}