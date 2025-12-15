package controllers;

import entite.Medicament;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import service.MedicamentService;
import test.MainFx;

import java.time.LocalDate;

public class MedicamentUpdateController {

    private final MedicamentService medicamentService = new MedicamentService();
    private Medicament selectedMedicament;

    // Form components
    @FXML private TextField medicamentName;
    @FXML private TextArea medicamentDescription;
    @FXML private Spinner<Integer> stockSpinner;
    @FXML private Spinner<Double> prixSpinner;
    @FXML private DatePicker dateEntreePicker;
    @FXML private DatePicker dateExpirationPicker;
    @FXML private ComboBox<String> typeComboBox;

    // Error labels
    @FXML private Label nameError;
    @FXML private Label descriptionError;
    @FXML private Label stockError;
    @FXML private Label prixError;
    @FXML private Label dateError;

    @FXML
    private void initialize() {
        configureSpinners();
        configureTypeComboBox();
    }

    private void configureSpinners() {
        stockSpinner.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 1000, 1));
        prixSpinner.setValueFactory(new SpinnerValueFactory.DoubleSpinnerValueFactory(0.1, 10000.0, 10.0, 0.5));
    }

    private void configureTypeComboBox() {
        typeComboBox.getItems().addAll("Comprimé ", "Capsule", "Sirops", "Poudre" , "Solutions buvables " , "Ampoule" , "Seringue" , "Aérosol" , "Crème" , "Lotion" ,"Suppositoire ");
    }

    public void setMedicament(Medicament medicament) {
        this.selectedMedicament = medicament;

        // Pré-remplir les champs
        medicamentName.setText(medicament.getNom_medicament());
        medicamentDescription.setText(medicament.getDescription_medicament());
        typeComboBox.setValue(medicament.getType_medicament());
        prixSpinner.getValueFactory().setValue(medicament.getPrix_medicament());
        stockSpinner.getValueFactory().setValue(medicament.getQuantite_stock());
        dateEntreePicker.setValue(medicament.getDate_entree());
        dateExpirationPicker.setValue(medicament.getDate_expiration());
    }

    @FXML
    private void handleUpdateMedicament() {
        clearErrors();

        String name = medicamentName.getText().trim();
        String description = medicamentDescription.getText().trim();
        String type = typeComboBox.getValue();
        int stock = stockSpinner.getValue();
        double prix = prixSpinner.getValue();
        LocalDate dateEntree = dateEntreePicker.getValue();
        LocalDate dateExpiration = dateExpirationPicker.getValue();

        if (!validateForm(name, description, type, stock, prix, dateEntree, dateExpiration)) return;

        // Modifier les données
        selectedMedicament.setNom_medicament(name);
        selectedMedicament.setDescription_medicament(description);
        selectedMedicament.setType_medicament(type);
        selectedMedicament.setPrix_medicament(prix);
        selectedMedicament.setQuantite_stock(stock);
        selectedMedicament.setDate_entree(dateEntree);
        selectedMedicament.setDate_expiration(dateExpiration);

        medicamentService.update(selectedMedicament);
        showAlert("Succès", "Médicament modifié avec succès !");
        MainFx.loadPage("medicament_list.fxml");
    }

    @FXML
    private void handleBackButton() {
        MainFx.loadPage("medicament_list.fxml");
    }

    private boolean validateForm(String name, String description, String type,
                                 int stock, double prix, LocalDate dateEntree,
                                 LocalDate dateExpiration) {
        boolean valid = true;

        // Vérifie que le nom contient uniquement des lettres et des espaces
        if (name.isEmpty() || name.length() < 2 || !name.matches("^[A-Za-zÀ-ÿ\\s]+$")) {
            nameError.setText("Nom invalide (min 2 lettres, sans chiffres) !");
            valid = false;
        }

        if (description.isEmpty()) {
            descriptionError.setText("Description requise !");
            valid = false;
        }

        if (type == null) {
            dateError.setText("Type requis !");
            valid = false;
        }

        if (stock <= 0) {
            stockError.setText("Stock doit être supérieur à 0 !");
            valid = false;
        }

        if (prix <= 0) {
            prixError.setText("Prix doit être supérieur à 0 !");
            valid = false;
        }

        if (dateEntree == null || dateExpiration == null) {
            dateError.setText("Les deux dates sont requises !");
            valid = false;
        } else if (dateExpiration.isBefore(dateEntree)) {
            dateError.setText("Date d'expiration doit être après la date d'entrée !");
            valid = false;
        }

        return valid;
    }

    private void clearErrors() {
        nameError.setText("");
        descriptionError.setText("");
        stockError.setText("");
        prixError.setText("");
        dateError.setText("");
    }

    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}
