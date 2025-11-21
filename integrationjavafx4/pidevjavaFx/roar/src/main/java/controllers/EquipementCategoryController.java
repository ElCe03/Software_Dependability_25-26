package controllers;

import entite.Equipement;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.layout.HBox;
import javafx.stage.Stage;
import service.EquipementService;
import javafx.scene.layout.VBox;


import java.io.IOException;
import java.util.List;

public class EquipementCategoryController {

    @FXML
    private Label categoryLabel;
    @FXML
    private TextField searchBar;
    @FXML
    private Button ajouterEquipementButton;
    @FXML
    private ListView<Equipement> equipementList;
    @FXML
    private Label noEquipementsLabel;
    @FXML
    private Label labelNomCategorie;
    /*@
          @ private invariant equipements != null;
          @ private invariant equipementService != null;
          @ private invariant equipementList != null;
          @*/
    private ObservableList<Equipement> equipements;
    private EquipementService equipementService;
    private String currentCategory;
    /*@ public normal_behavior
          @   requires equipementList != null;
          @   requires noEquipementsLabel != null;
          @   assignable equipementService, equipements,
          @              equipementList.items, equipementList.cellFactory;
          @   ensures equipementService != null;
          @   ensures equipements != null;
          @   ensures equipementList.getItems() == equipements;
          @*/
    public void initialize() {
        equipementService = new EquipementService();
        equipements = FXCollections.observableArrayList();
        equipementList.setItems(equipements);
        setCustomCellFactory();
    }
    /*@ public normal_behavior
          @   requires categoryName != null;
          @   requires labelNomCategorie != null && categoryLabel != null;
          @   requires equipementService != null; // da initialize
          @   assignable currentCategory, labelNomCategorie.text, categoryLabel.text,
          @              equipements, noEquipementsLabel.visible;
          @   ensures this.currentCategory == categoryName;
          @   ensures labelNomCategorie.getText().equals(categoryName);
          @   ensures !equipements.isEmpty() ==> !noEquipementsLabel.isVisible();
          @*/
    public void setCategorie(String categoryName) {
        labelNomCategorie.setText(categoryName);
        currentCategory = categoryName;
        categoryLabel.setText("Catégorie : " + categoryName);
        chargerEquipementsParCategorie();
    }

    public void setCategoryTitle(String categoryName) {
        currentCategory = categoryName;
        categoryLabel.setText("Catégorie : " + categoryName);
        chargerEquipementsParCategorie();
    }
    /*@ private normal_behavior
         @   requires currentCategory != null;
         @   requires equipementService != null && equipements != null;
         @   assignable equipements, noEquipementsLabel.visible;
         @*/
    private void chargerEquipementsParCategorie() {
        try {
            if (currentCategory == null || currentCategory.isEmpty()) {
                System.err.println("❌ La catégorie n'est pas définie !");
                return;
            }

            List<Equipement> equipementListFromDB = equipementService.getEquipementsByCategory(currentCategory);
            listEquipementsInVBox(equipementListFromDB);

        } catch (Exception e) {
            System.err.println("❌ Erreur lors du chargement des équipements : " + e.getMessage());
        }
    }
    /*@ private normal_behavior
          @   requires equipementsFromDB != null;
          @   requires this.equipements != null;
          @   assignable this.equipements, noEquipementsLabel.visible;
          @   ensures this.equipements.size() == equipementsFromDB.size();
          @   ensures equipementsFromDB.isEmpty() <==> noEquipementsLabel.isVisible();
          @*/
    private void listEquipementsInVBox(List<Equipement> equipementsFromDB) {
        this.equipements.clear();

        if (equipementsFromDB.isEmpty()) {
            noEquipementsLabel.setVisible(true);
        } else {
            noEquipementsLabel.setVisible(false);
            this.equipements.addAll(equipementsFromDB);
        }
    }

    @FXML
    private void handleAjouterEquipement() {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/ajouter_equipement.fxml"));
            Parent ajouterEquipementForm = loader.load();

            AjouterEquipementController controller = loader.getController();
            controller.setCategorie(currentCategory);

            // ➕ Ajout du callback pour rafraîchir la liste après ajout
            controller.setOnEquipementAjoute(() -> {
                // Recharger les équipements depuis la base
                chargerEquipementsParCategorie();
            });

            Stage newStage = new Stage();
            newStage.setTitle("Ajouter un Équipement");
            newStage.setScene(new Scene(ajouterEquipementForm));
            newStage.show();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /*@ private normal_behavior
          @   requires searchBar != null;
          @   requires equipements != null; // Lista master
          @   requires equipementList != null; // Vista UI
          @   assignable equipementList.items, noEquipementsLabel.visible;
          @   ensures (\forall Equipement eq; equipementList.getItems().contains(eq);
          @            equipements.contains(eq));
          @*/
    @FXML
    private void filterEquipements() {
        String searchTerm = searchBar.getText().toLowerCase();
        ObservableList<Equipement> filtered = FXCollections.observableArrayList();

        for (Equipement eq : equipements) {
            if (eq.getNom().toLowerCase().contains(searchTerm) ||
                    eq.getType().toLowerCase().contains(searchTerm) ||
                    eq.getStatut().toLowerCase().contains(searchTerm)) {
                filtered.add(eq);
            }
        }

        equipementList.setItems(filtered);
        noEquipementsLabel.setVisible(filtered.isEmpty());
    }

    private void setCustomCellFactory() {
        equipementList.setCellFactory(listView -> new ListCell<Equipement>() {
            private final HBox content = new HBox(20); // espace entre les éléments
            private final Label infosLabel = new Label();

            private final Button btnModifier = new Button("Modifier");
            private final Button btnSupprimer = new Button("Supprimer");
            private final Button btnEntretien = new Button("Entretien");

            {
                // Style des infos : une seule ligne, en gras
                infosLabel.setStyle("-fx-font-weight: bold; -fx-font-size: 14px;");

                // Espacement et centrage
                content.setSpacing(20);
                content.getChildren().addAll(infosLabel, btnModifier, btnSupprimer, btnEntretien);

                // Style des boutons
                btnModifier.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white;");
                btnSupprimer.setStyle("-fx-background-color: #F44336; -fx-text-fill: white;");
                btnEntretien.setStyle("-fx-background-color: #008CBA; -fx-text-fill: white;");

                // Actions des boutons
                btnModifier.setOnAction(e -> {
                    Equipement equipement = getItem();
                    if (equipement != null) {
                        handleModifierEquipement(equipement);
                    }
                });

                btnSupprimer.setOnAction(e -> {
                    Equipement equipement = getItem();
                    if (equipement != null) {
                        handleSupprimerEquipement(equipement);
                    }
                });

                btnEntretien.setOnAction(e -> {
                    Equipement equipement = getItem();
                    if (equipement != null) {
                        ouvrirFormulaireEntretien(equipement);
                    }
                });
            }

            @Override
            protected void updateItem(Equipement equipement, boolean empty) {
                super.updateItem(equipement, empty);
                if (empty || equipement == null) {
                    setGraphic(null);
                } else {
                    infosLabel.setText("Nom : " + equipement.getNom() +
                            "     Type : " + equipement.getType() +
                            "     Statut : " + equipement.getStatut());
                    setGraphic(content);
                }
            }
        });
    }





    private void handleModifierEquipement(Equipement equipement) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/ModifierEquipement.fxml"));
            Parent root = loader.load();

            ModifierEquipementController controller = loader.getController();
            controller.initData(equipement);

            // 🔁 Rafraîchissement après modification
            controller.setOnEquipementModifie(() -> {
                chargerEquipementsParCategorie();
            });

            Stage stage = new Stage();
            stage.setTitle("Modifier Équipement");
            stage.setScene(new Scene(root));
            stage.show();
        } catch (IOException e) {
            System.err.println("❌ Erreur lors du chargement de la page de modification : " + e.getMessage());
        }
    }


    private void handleSupprimerEquipement(Equipement equipement) {
        equipementService.supprimerEquipement(equipement.getId());
        equipements.remove(equipement);
        System.out.println("🗑 Supprimé : " + equipement.getNom());
    }

    private void ouvrirFormulaireEntretien(Equipement equipement) {
        try {
            // Ouvrir le formulaire d'entretien sans changer le statut de l'équipement tout de suite
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/ajouter_entretien.fxml"));
            Parent root = loader.load();

            AjouterEntretienController controller = loader.getController();
            controller.setEquipement(equipement);

            // Ajouter un callback pour mettre à jour le statut après la création de l'entretien
            controller.setOnEntretienAjoute(() -> {
                // Après l'ajout de l'entretien, changer le statut de l'équipement à "maintenance"
                equipement.setStatut("maintenance");
                equipementService.modifierEquipement(equipement); // mettre à jour le statut dans la base de données

                // Recharger les équipements pour voir la mise à jour immédiatement
                chargerEquipementsParCategorie();
            });

            Stage stage = new Stage();
            stage.setTitle("Ajouter un entretien");
            stage.setScene(new Scene(root));
            stage.show();

        } catch (IOException e) {
            System.err.println("❌ Erreur ouverture formulaire entretien : " + e.getMessage());
        }
    }


}