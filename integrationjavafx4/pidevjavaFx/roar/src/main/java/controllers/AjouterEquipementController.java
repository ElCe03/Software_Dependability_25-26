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

    // ✅ Ajouté pour gérer la zone dynamique
    private VBox contentArea;

    private EquipementService equipementService;

    private Runnable onEquipementAjoute;

    private EquipementService getEquipementService() {
        if (this.equipementService == null) {
            this.equipementService = new EquipementService();
        }
        return this.equipementService;
    }

    public void setEquipementService(EquipementService equipementService) {
        this.equipementService = equipementService;
    }

    // ✅ Setter pour contentArea (appelé par le contrôleur principal)
    public void setContentArea(VBox contentArea) {
        this.contentArea = contentArea;
    }

    public void setCategorie(String categorie) {
        categoryField.setText(categorie);
        categoryField.setEditable(false);
    }

    public void setOnEquipementAjoute(Runnable callback) {
        this.onEquipementAjoute = callback;
    }

    @FXML
    private void handleEnregistrer() {
        try {
            Equipement nouvelEquipement = buildEquipementFromFields(
                    nomField.getText(),
                    typeField.getText(),
                    statutCombo.getValue(),
                    categoryField.getText()
            );

            
            getEquipementService().ajouterEquipement(nouvelEquipement);

            showAlert(Alert.AlertType.INFORMATION, "Succès", "L’équipement a été ajouté avec succès !");

            if (onEquipementAjoute != null) {
                onEquipementAjoute.run();
            }

            // ✅ Nouvelle logique pour revenir à la vue equipement_category.fxml
            if (contentArea != null) {
                try {
                    FXMLLoader loader = new FXMLLoader(getClass().getResource("/equipement_category.fxml"));
                    Parent categoryView = loader.load();

                    // Transmettre la catégorie à la nouvelle vue :
                    EquipementCategoryController controller = loader.getController();
                    controller.setCategorie(categoryField.getText());

                    contentArea.getChildren().setAll(categoryView);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }

        } catch (IllegalArgumentException e) {
            showAlert(Alert.AlertType.WARNING, "Champs manquants", e.getMessage());
        }
    }

    private void showAlert(Alert.AlertType type, String title, String message) {
        Alert alert = new Alert(type);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    public void initData(Equipement equipement) {
        nomField.setText(equipement.getNom());
        typeField.setText(equipement.getType());
        statutCombo.setValue(equipement.getStatut());
        categoryField.setText(equipement.getCategory());

        categoryField.setEditable(false);
    }

    private Equipement buildEquipementFromFields(
            String nom, String type, String statut, String categorie
    ) {
        if (nom == null || nom.trim().isEmpty()
                || type == null || type.trim().isEmpty()
                || statut == null || statut.trim().isEmpty()
                || categorie == null || categorie.trim().isEmpty()) {
            throw new IllegalArgumentException("Champs manquants");
        }

        Equipement e = new Equipement();
        e.setNom(nom.trim());
        e.setType(type.trim());
        e.setStatut(statut.trim());
        e.setCategory(categorie.trim());

        return e;
    }
}