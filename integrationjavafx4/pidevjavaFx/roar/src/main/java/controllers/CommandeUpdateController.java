package controllers;

import entite.Commande;
import entite.Medicament;
import entite.MedicamentCommande;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import service.CommandeService;
import service.MedicamentService;
import test.MainFx;

import java.time.LocalDate;

public class CommandeUpdateController {

    @FXML private DatePicker dateCommandePicker;
    @FXML private Spinner<Integer> quantiteSpinner;
    @FXML private ComboBox<Medicament> medicamentComboBox;
    @FXML private TextField quantiteMedicamentField;
    @FXML private ListView<String> medicamentListView;
    @FXML private Label totalPrixLabel;

    @FXML private Label dateError;
    @FXML private Label medicamentError;
    @FXML private Label quantiteError;

    private Commande commande;
    private final ObservableList<MedicamentCommande> medicamentCommandes = FXCollections.observableArrayList();
    private final MedicamentService medicamentService = new MedicamentService();
    private final CommandeService commandeService = new CommandeService();

    @FXML
    private void initialize() {
        medicamentComboBox.setItems(FXCollections.observableArrayList(medicamentService.readAll()));

        medicamentComboBox.setCellFactory(lv -> new ListCell<>() {
            @Override
            protected void updateItem(Medicament medicament, boolean empty) {
                super.updateItem(medicament, empty);
                setText(empty || medicament == null ? null : medicament.getNom_medicament());
            }
        });

        medicamentComboBox.setButtonCell(new ListCell<>() {
            @Override
            protected void updateItem(Medicament medicament, boolean empty) {
                super.updateItem(medicament, empty);
                setText(empty || medicament == null ? null : medicament.getNom_medicament());
            }
        });

        quantiteSpinner.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 1000, 1));
    }

    public void setCommande(Commande commande) {
        this.commande = commande;

        dateCommandePicker.setValue(commande.getDate_commande());
        quantiteSpinner.getValueFactory().setValue(commande.getQuantite());

        // Ensure status is not null
        if (commande.getStatus() == null) {
            commande.setStatus("pending");
        }

        medicamentCommandes.setAll(commande.getMedicaments());
        medicamentListView.getItems().clear();
        for (MedicamentCommande mc : medicamentCommandes) {
            medicamentListView.getItems().add(
                    mc.getMedicament().getNom_medicament() + " x" + mc.getQuantite()
            );
        }

        updateTotalPrix();
    }

    @FXML
    private void handleAddMedicamentToCommande() {
        clearErrors();

        Medicament medicament = medicamentComboBox.getValue();
        int quantite = quantiteSpinner.getValue();
        boolean isValid = true;

        if (medicament == null) {
            medicamentError.setText("Médicament requis.");
            isValid = false;
        }

        if (quantite <= 0) {
            quantiteError.setText("Quantité invalide.");
            isValid = false;
        } else if (medicament != null && quantite > medicament.getQuantite_stock()) {
            quantiteError.setText("Stock insuffisant (max: " + medicament.getQuantite_stock() + ").");
            isValid = false;
        }

        if (!isValid) return;

        MedicamentCommande mc = new MedicamentCommande(commande, medicament, quantite);
        medicamentCommandes.add(mc);
        medicamentListView.getItems().add(medicament.getNom_medicament() + " x" + quantite);

        updateTotalPrix();
    }

    @FXML
    private void handleUpdateCommande() {
        clearErrors();

        LocalDate dateCommande = dateCommandePicker.getValue();
        boolean isValid = true;

        if (dateCommande == null) {
            dateError.setText("Date requise.");
            isValid = false;
        } else if (dateCommande.isBefore(LocalDate.now())) {
            dateError.setText("La date ne peut pas être dans le passé.");
            isValid = false;
        }

        if (medicamentCommandes.isEmpty()) {
            showAlert("Erreur", "Veuillez ajouter au moins un médicament.");
            return;
        }

        if (!isValid) return;

        double totalPrix = calculateTotal();

        commande.setDate_commande(dateCommande);
        commande.setQuantite(medicamentCommandes.stream().mapToInt(MedicamentCommande::getQuantite).sum());
        commande.setTotal_prix(totalPrix);
        commande.getMedicaments().clear();
        commande.getMedicaments().addAll(medicamentCommandes);

        // Ensure status is set
        if (commande.getStatus() == null) {
            commande.setStatus("pending");
        }

        commandeService.update(commande);

        showAlert("Succès", "Commande mise à jour avec succès !");
        MainFx.loadPage("commande_list.fxml");
    }

    private double calculateTotal() {
        return medicamentCommandes.stream()
                .mapToDouble(mc -> mc.getMedicament().getPrix_medicament() * mc.getQuantite())
                .sum();
    }

    private void updateTotalPrix() {
        totalPrixLabel.setText(String.format("%.2f DT", calculateTotal()));
    }

    private void showAlert(String titre, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(titre);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    @FXML
    private void handleClearCommande() {
        dateCommandePicker.setValue(null);
        quantiteSpinner.getValueFactory().setValue(1);
        medicamentListView.getItems().clear();
        medicamentCommandes.clear();
        medicamentComboBox.getSelectionModel().clearSelection();
        quantiteMedicamentField.clear();
        totalPrixLabel.setText("0.00 DT");
        clearErrors();
    }

    private void clearErrors() {
        dateError.setText("");
        medicamentError.setText("");
        quantiteError.setText("");
    }
}