package controllers;

import entite.Equipement;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.control.*;
import javafx.scene.layout.VBox;
import service.EquipementService;

import java.io.IOException;

public class AjouterEquipementController {


    @FXML
    private TextField nomField;


    @FXML
    private TextField typeField;


    @FXML
    private ComboBox<String> statutCombo;


    @FXML
    private TextField categoryField;


    private VBox contentArea;


    private final EquipementService equipementService = new EquipementService();


    private Runnable onEquipementAjoute;

    /*@ public invariant equipementService != null;
      @*/

    /*@
      @ ensures this.contentArea == contentArea;
      @ assignable this.contentArea;
      @*/
    public void setContentArea(VBox contentArea) {
        this.contentArea = contentArea;
    }

    /*@
      @ requires categorie != null;
      @ requires categoryField != null;
      @ ensures categoryField.getText().equals(categorie);
      @ ensures !categoryField.isEditable();
      @ assignable categoryField.text, categoryField.editable;
      @*/
    public void setCategorie(String categorie) {
        //@ assert categorie != null;
        //@ assert categoryField != null;

        categoryField.setText(categorie);
        categoryField.setEditable(false);
    }

    /*@
      @ ensures this.onEquipementAjoute == callback;
      @ assignable this.onEquipementAjoute;
      @*/
    public void setOnEquipementAjoute(Runnable callback) {
        this.onEquipementAjoute = callback;
    }

    /*@
      @ requires nomField != null;
      @ requires typeField != null;
      @ requires statutCombo != null;
      @ requires categoryField != null;
      @ requires equipementService != null;
      @ assignable equipementService.*, contentArea.*;
      @*/
    @FXML
    private void handleEnregistrer() {
        //@ assert nomField != null;
        //@ assert typeField != null;
        //@ assert statutCombo != null;
        //@ assert categoryField != null;

        String nom = nomField.getText().trim();
        String type = typeField.getText().trim();
        String statut = statutCombo.getValue();
        String categorie = categoryField.getText().trim();

        //@ assert nom != null;
        //@ assert type != null;
        //@ assert categorie != null;

        // Validate required fields
        if (nom.isEmpty() || type.isEmpty() || statut == null || categorie.isEmpty()) {
            showAlert(Alert.AlertType.WARNING, "Champs manquants", "Veuillez remplir tous les champs !");
            return;
        }

        //@ assert !nom.isEmpty();
        //@ assert !type.isEmpty();
        //@ assert statut != null;
        //@ assert !categorie.isEmpty();

        // Create new equipment
        Equipement nouvelEquipement = new Equipement();
        //@ assert nouvelEquipement != null;

        nouvelEquipement.setNom(nom);
        nouvelEquipement.setType(type);
        nouvelEquipement.setStatut(statut);
        nouvelEquipement.setCategory(categorie);

        //@ assert nouvelEquipement.getNom() == nom;
        //@ assert nouvelEquipement.getType() == type;
        //@ assert nouvelEquipement.getStatut() == statut;
        //@ assert nouvelEquipement.getCategory() == categorie;

        // Save equipment
        equipementService.ajouterEquipement(nouvelEquipement);

        showAlert(Alert.AlertType.INFORMATION, "Succès", "L'équipement a été ajouté avec succès !");

        // Execute callback if set
        if (onEquipementAjoute != null) {
            //@ assert onEquipementAjoute != null;
            onEquipementAjoute.run();
        }

        // Navigate back to category view
        if (contentArea != null) {
            //@ assert contentArea != null;

            try {
                FXMLLoader loader = new FXMLLoader(getClass().getResource("/equipement_category.fxml"));
                //@ assert loader != null;

                Parent categoryView = loader.load();
                //@ assert categoryView != null;

                // Pass category to new view
                EquipementCategoryController controller = loader.getController();
                //@ assert controller != null;

                controller.setCategorie(categorie);

                contentArea.getChildren().setAll(categoryView);
            } catch (IOException e) {
                //@ assert e != null;
                e.printStackTrace();
            }
        }
    }

    /*@
      @ requires type != null;
      @ requires title != null;
      @ requires message != null;
      @ requires !title.isEmpty();
      @ requires !message.isEmpty();
      @*/
    private void showAlert(Alert.AlertType type, String title, String message) {
        //@ assert type != null;
        //@ assert title != null && !title.isEmpty();
        //@ assert message != null && !message.isEmpty();

        Alert alert = new Alert(type);
        //@ assert alert != null;

        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    /*@
      @ requires equipement != null;
      @ requires equipement.getNom() != null;
      @ requires equipement.getType() != null;
      @ requires equipement.getStatut() != null;
      @ requires equipement.getCategory() != null;
      @ requires nomField != null;
      @ requires typeField != null;
      @ requires statutCombo != null;
      @ requires categoryField != null;
      @ ensures nomField.getText().equals(equipement.getNom());
      @ ensures typeField.getText().equals(equipement.getType());
      @ ensures statutCombo.getValue().equals(equipement.getStatut());
      @ ensures categoryField.getText().equals(equipement.getCategory());
      @ ensures !categoryField.isEditable();
      @ assignable nomField.text, typeField.text, statutCombo.value,
      @            categoryField.text, categoryField.editable;
      @*/
    public void initData(Equipement equipement) {
        //@ assert equipement != null;
        //@ assert equipement.getNom() != null;
        //@ assert equipement.getType() != null;
        //@ assert equipement.getStatut() != null;
        //@ assert equipement.getCategory() != null;
        //@ assert nomField != null;
        //@ assert typeField != null;
        //@ assert statutCombo != null;
        //@ assert categoryField != null;

        nomField.setText(equipement.getNom());
        typeField.setText(equipement.getType());
        statutCombo.setValue(equipement.getStatut());
        categoryField.setText(equipement.getCategory());

        //@ assert nomField.getText().equals(equipement.getNom());
        //@ assert typeField.getText().equals(equipement.getType());
        //@ assert statutCombo.getValue().equals(equipement.getStatut());
        //@ assert categoryField.getText().equals(equipement.getCategory());

        categoryField.setEditable(false);

        //@ assert !categoryField.isEditable();
    }
}
