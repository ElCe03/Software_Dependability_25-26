package controllers;

import entite.Entretien;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import service.EntretienService;
import javafx.stage.Stage;

import java.time.LocalDate;

public class ModifierEntretienController {

    @FXML
    private TextField nomEquipementField;

    @FXML
    private DatePicker datePicker;

    @FXML
    private TextArea descriptionArea;

    private Entretien entretien;

    private EntretienService entretienService;

    private Runnable onEntretienModifie; // ✅ Callback pour rafraîchir la liste

    private EntretienService getEntretienService() {
        if (this.entretienService == null) {
            this.entretienService = new EntretienService();
        }
        return this.entretienService;
    }

    public void setEntretienService(EntretienService entretienService) {
        this.entretienService = entretienService;
    }

    // Méthode pour initialiser les données de l'entretien à modifier
    public void initData(Entretien entretien) {
        this.entretien = entretien;
        nomEquipementField.setText(entretien.getNomEquipement());
        datePicker.setValue(entretien.getDate());
        descriptionArea.setText(entretien.getDescription());
    }

    // Setter pour le callback
    public void setOnEntretienModifie(Runnable onEntretienModifie) {
        this.onEntretienModifie = onEntretienModifie;
    }

    // Méthode pour mettre à jour l'entretien dans la base de données
    @FXML
    private void handleUpdate() {
        String nom = nomEquipementField.getText().trim();
        String description = descriptionArea.getText().trim();
        LocalDate selectedDate = datePicker.getValue();

        // Validation des champs
        try {
            buildUpdatedEntretien(this.entretien, nom, description, selectedDate);

            getEntretienService().updateEntretien(this.entretien);

            // Rafraîchissement de la liste après mise à jour
            if (onEntretienModifie != null) {
                onEntretienModifie.run();
            }

            showAlert("Succès", "L'entretien a été modifié avec succès.");
            ((Stage) nomEquipementField.getScene().getWindow()).close();

        } catch (IllegalArgumentException e) {
            showAlert("Erreur", e.getMessage());
        } catch (Exception e) {
            showAlert("Erreur", "Une erreur est survenue lors de la mise à jour : " + e.getMessage());
        }
    }

    // Méthode utilitaire pour afficher des alertes
    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    public Entretien buildUpdatedEntretien(
            Entretien entretien,
            String nom,
            String description,
            LocalDate selectedDate
    ) {
        if (entretien == null) {
             throw new IllegalArgumentException("Champs manquants");
        }
        
        if (nom == null || nom.trim().isEmpty() ||
                description == null || description.trim().isEmpty() ||
                selectedDate == null) {
            throw new IllegalArgumentException("Champs manquants");
        }

        if (selectedDate.isBefore(LocalDate.now())) {
            throw new IllegalArgumentException("Date invalide");
        }

        entretien.setNomEquipement(nom.trim());
        entretien.setDescription(description.trim());
        entretien.setDate(selectedDate);

        return entretien;
    }
}