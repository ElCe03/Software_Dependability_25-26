package controllers;

import entite.Entretien;
import entite.Equipement;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.stage.Stage;
import service.EntretienService;
import service.EquipementService;
import service.MailService;

import java.io.IOException;
import java.time.LocalDate;
import java.time.LocalDateTime;

public class AjouterEntretienController {

    @FXML
    private Label titleLabel;

    @FXML
    private TextField nomEquipementField;

    @FXML
    private DatePicker dateEntretienPicker;

    @FXML
    private TextArea descriptionField;

    private Equipement equipement;

    private final EntretienService entretienService = new EntretienService();

    private final EquipementService equipementService = new EquipementService();

    private Runnable onEntretienAjoute;

    /*@ public invariant entretienService != null;
      @ public invariant equipementService != null;
      @*/

    /*@
      @ requires equipement != null ==> equipement.getNom() != null;
      @ ensures this.equipement == equipement;
      @ ensures equipement != null ==>
      @     nomEquipementField.getText().equals(equipement.getNom());
      @ ensures equipement != null ==> !nomEquipementField.isEditable();
      @ ensures equipement != null ==>
      @     titleLabel.getText().contains(equipement.getNom());
      @ assignable this.equipement, nomEquipementField.text,
      @            nomEquipementField.editable, titleLabel.text;
      @*/
    public void setEquipement(Equipement equipement) {
        this.equipement = equipement;

        if (equipement != null) {
            nomEquipementField.setText(equipement.getNom());
            nomEquipementField.setEditable(false);
            titleLabel.setText("Créer un entretien pour l'équipement " + equipement.getNom());
        }
    }

    /*@
      @ ensures this.onEntretienAjoute == onEntretienAjoute;
      @ assignable this.onEntretienAjoute;
      @*/
    public void setOnEntretienAjoute(Runnable onEntretienAjoute) {
        this.onEntretienAjoute = onEntretienAjoute;
    }

    /*@
      @ requires nomEquipementField != null;
      @ requires descriptionField != null;
      @ requires dateEntretienPicker != null;
      @ requires entretienService != null;
      @ assignable entretienService.*, nomEquipementField.scene.window.*;
      @*/
    @FXML
    private void handleCreateEntretien() {
        // Early return if no equipment is set
        if (equipement == null) {
            System.err.println("Aucun équipement défini !");
            return;
        }

        //@ assert equipement != null;
        //@ assert equipement.getNom() != null;
        //@ assert equipement.getId() != null || equipement.getId() >= 0;

        String description = descriptionField.getText().trim();
        LocalDate selectedDate = dateEntretienPicker.getValue();

        //@ assert description != null;

        // Validation: check required fields
        if (description.isEmpty() || selectedDate == null) {
            showAlert("Erreur", "Tous les champs doivent être remplis.");
            return;
        }

        //@ assert !description.isEmpty();
        //@ assert selectedDate != null;

        // Validation: check date is not in the past
        if (selectedDate.isBefore(LocalDate.now())) {
            showAlert("Erreur", "La date de l'entretien ne peut pas être dans le passé.");
            return;
        }

        //@ assert !selectedDate.isBefore(LocalDate.now());

        // Create maintenance entry
        Entretien entretien = new Entretien();
        //@ assert entretien != null;

        entretien.setNomEquipement(equipement.getNom());
        entretien.setDescription(description);
        entretien.setDate(selectedDate);
        entretien.setEquipementId(equipement.getId());
        entretien.setCreatedAt(LocalDateTime.now());

        //@ assert entretien.getNomEquipement() == equipement.getNom();
        //@ assert entretien.getDescription() == description;
        //@ assert entretien.getDate() == selectedDate;

        // Save maintenance entry
        entretienService.ajouterEntretien(entretien);

        // Send email notification
        String emailUtilisateur = "bouhjarmariem012@gmail.com";
        //@ assert emailUtilisateur != null;
        //@ assert emailUtilisateur.contains("@");

        String sujet = "Nouvel entretien créé";
        //@ assert sujet != null;

        String message = "Bonjour,\n\nUn nouvel entretien a été enregistré pour l'équipement : " +
                equipement.getNom() + "\nDate prévue : " + selectedDate +
                "\n\nStatut : En maintenance.\n\nMerci.";
        //@ assert message != null;

        MailService.sendEmail(emailUtilisateur, sujet, message);

        // Notify callback if set
        if (onEntretienAjoute != null) {
            //@ assert onEntretienAjoute != null;
            onEntretienAjoute.run();
        }

        // Navigate to maintenance list
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/liste_entretien.fxml"));
            //@ assert loader != null;

            Parent root = loader.load();
            //@ assert root != null;

            Stage stage = new Stage();
            //@ assert stage != null;

            stage.setTitle("Liste des entretiens");
            stage.setScene(new Scene(root));
            stage.show();

            // Close current window
            nomEquipementField.getScene().getWindow().hide();

        } catch (IOException e) {
            //@ assert e != null;
            System.err.println("Erreur lors du chargement de la liste : " + e.getMessage());
        }
    }

    /*@
      @ requires title != null;
      @ requires message != null;
      @ requires !title.isEmpty();
      @ requires !message.isEmpty();
      @*/
    private void showAlert(String title, String message) {
        //@ assert title != null && !title.isEmpty();
        //@ assert message != null && !message.isEmpty();

        Alert alert = new Alert(Alert.AlertType.ERROR);
        //@ assert alert != null;

        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}