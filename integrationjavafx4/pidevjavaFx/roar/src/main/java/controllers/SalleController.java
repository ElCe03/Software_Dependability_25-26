package controllers;

import entite.salle;
import entite.etage;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import service.EtageService;
import service.SalleService;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class SalleController {

    // Champs du formulaire
    @FXML
    private TextField nomField;
    @FXML
    private TextField capaciteField;
    @FXML
    private ComboBox<String> typeCombo;
    @FXML
    private ComboBox<String> statusCombo;
    @FXML
    private Spinner<Integer> prioriteSpinner;
    @FXML
    private ComboBox<etage> etageCombo;
    @FXML
    private TextField imageField;
    @FXML
    private ImageView imagePreview;

    // Messages d'erreur
    @FXML
    private Label nomError;
    @FXML
    private Label capaciteError;
    @FXML
    private Label typeError;
    @FXML
    private Label statusError;
    @FXML
    private Label prioriteError;
    @FXML
    private Label etageError;
    @FXML
    private Label imageError;

    // TableView et colonnes
    @FXML
    private TableView<salle> salleTable;
    @FXML
    private TableColumn<salle, String> nomColumn;
    @FXML
    private TableColumn<salle, Integer> capaciteColumn;
    @FXML
    private TableColumn<salle, String> typeColumn;
    @FXML
    private TableColumn<salle, String> statusColumn;
    @FXML
    private TableColumn<salle, Integer> prioriteColumn;
    @FXML
    private TableColumn<salle, etage> etageColumn;
    @FXML
    private TableColumn<salle, String> imageColumn;
    @FXML
    private TableColumn<salle, Void> actionsColumn;

    // Boutons
    @FXML
    private Button saveBtn;
    @FXML
    private Button clearBtn;
    @FXML
    private Button browseBtn;
    @FXML
    private Button exportBtn;

    // Search field
    @FXML
    private TextField searchField;

    // Services et données
    private final SalleService salleService = new SalleService();
    private final EtageService etageService = new EtageService();
    private final ObservableList<salle> salleData = FXCollections.observableArrayList();
    private final ObservableList<salle> filteredSalleData = FXCollections.observableArrayList();
    private String imagePath = "";
    public static final String IMAGE_DIR = "src/main/resources/images/";

    @FXML
    public void initialize() {
        createImageDirectory();
        setupForm();
        setupTable();
        loadSalles();
        setupSearch();
    }

    private void createImageDirectory() {
        File imageDir = new File(IMAGE_DIR);
        if (!imageDir.exists()) {
            imageDir.mkdirs();
        }
    }

    private void setupForm() {
        // Configuration des ComboBox
        typeCombo.setItems(FXCollections.observableArrayList(
                "Consultation", "Bloc opératoire", "Réanimation", "Chambre"));
        statusCombo.setItems(FXCollections.observableArrayList(
                "Disponible", "Occupée", "En maintenance"));

        // Configuration du Spinner pour la priorité (1-10)
        prioriteSpinner.setValueFactory(
                new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 10, 1));

        // Chargement des étages
        List<etage> etages = etageService.getAllEtages();
        etageCombo.setItems(FXCollections.observableArrayList(etages));

        // Afficher le numéro de l'étage dans le ComboBox
        etageCombo.setCellFactory(combo -> new ListCell<etage>() {
            @Override
            protected void updateItem(etage item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? "" : String.valueOf(item.getNumero()));
            }
        });
        etageCombo.setButtonCell(new ListCell<etage>() {
            @Override
            protected void updateItem(etage item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? "" : String.valueOf(item.getNumero()));
            }
        });
    }

    private void setupTable() {
        // Configuration des colonnes de données
        nomColumn.setCellValueFactory(new PropertyValueFactory<>("nom"));
        capaciteColumn.setCellValueFactory(new PropertyValueFactory<>("capacite"));
        typeColumn.setCellValueFactory(new PropertyValueFactory<>("type_salle"));
        statusColumn.setCellValueFactory(new PropertyValueFactory<>("status"));
        prioriteColumn.setCellValueFactory(new PropertyValueFactory<>("priorite"));
        etageColumn.setCellValueFactory(new PropertyValueFactory<>("etage"));
        imageColumn.setCellValueFactory(new PropertyValueFactory<>("image"));

        // Bind column widths to TableView width for responsiveness
        nomColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.15));
        capaciteColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.1));
        typeColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.15));
        statusColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.15));
        prioriteColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.1));
        etageColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.1));
        imageColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.15));
        actionsColumn.prefWidthProperty().bind(salleTable.widthProperty().multiply(0.15));

        // Configuration de la colonne status
        statusColumn.setCellFactory(column -> new TableCell<salle, String>() {
            @Override
            protected void updateItem(String status, boolean empty) {
                super.updateItem(status, empty);
                setText(null);
                setStyle("");

                if (!empty && status != null) {
                    setText(status);
                    switch (status) {
                        case "Occupée":
                            setStyle("-fx-text-fill: #EF5350; -fx-background-color: #FFEBEE;");
                            break;
                        case "Disponible":
                            setStyle("-fx-text-fill: #66BB6A; -fx-background-color: #E8F5E9;");
                            break;
                        case "En maintenance":
                            setStyle("-fx-text-fill: #FFCA28; -fx-background-color: #FFF8E1;");
                            break;
                        default:
                            setStyle("-fx-text-fill: #333333;");
                    }
                }
            }
        });

        // Configuration de la colonne image
        imageColumn.setCellFactory(column -> new TableCell<salle, String>() {
            private final ImageView imageView = new ImageView();
            private final Label label = new Label();

            {
                imageView.setFitHeight(40);
                imageView.setFitWidth(40);
                imageView.setPreserveRatio(true);
                label.setStyle("-fx-text-fill: #666666;");
            }

            @Override
            protected void updateItem(String imageName, boolean empty) {
                super.updateItem(imageName, empty);

                setGraphic(null);
                setText(null);

                if (!empty && imageName != null && !imageName.isEmpty()) {
                    try {
                        File imageFile = new File(IMAGE_DIR + imageName);
                        if (imageFile.exists()) {
                            imageView.setImage(new Image(imageFile.toURI().toString()));
                            setGraphic(imageView);
                        } else {
                            label.setText("Image manquante");
                            setGraphic(label);
                        }
                    } catch (Exception e) {
                        label.setText("Erreur");
                        setGraphic(label);
                    }
                }
            }
        });

        // Configuration de la colonne d'étage
        etageColumn.setCellFactory(column -> new TableCell<salle, etage>() {
            @Override
            protected void updateItem(etage etage, boolean empty) {
                super.updateItem(etage, empty);
                if (empty || etage == null) {
                    setText(null);
                } else {
                    setText(String.valueOf(etage.getNumero()));
                }
            }
        });

        // Configuration de la colonne d'actions
        actionsColumn.setCellFactory(column -> new TableCell<salle, Void>() {
            private final HBox buttons = new HBox(5);
            private final Button editBtn = new Button("✏");
            private final Button deleteBtn = new Button("🗑");

            {
                buttons.setStyle("-fx-alignment: CENTER;");
                editBtn.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white; -fx-font-size: 12px; -fx-background-radius: 5px;");
                deleteBtn.setStyle("-fx-background-color: #EF5350; -fx-text-fill: white; -fx-font-size: 12px; -fx-background-radius: 5px;");

                editBtn.setOnAction(event -> {
                    salle salle = getTableView().getItems().get(getIndex());
                    showEditDialog(salle);
                });

                deleteBtn.setOnAction(event -> {
                    salle salle = getTableView().getItems().get(getIndex());
                    confirmAndDelete(salle);
                });

                buttons.getChildren().addAll(editBtn, deleteBtn);
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                if (!empty) {
                    setGraphic(buttons);
                } else {
                    setGraphic(null);
                }
            }
        });
    }

    private void loadSalles() {
        salleData.clear();
        salleData.addAll(salleService.getAll());
        filteredSalleData.setAll(salleData);
        salleTable.setItems(filteredSalleData);
    }

    private void setupSearch() {
        searchField.textProperty().addListener((observable, oldValue, newValue) -> {
            filterSalles(newValue);
        });
    }

    private void filterSalles(String searchText) {
        if (searchText == null || searchText.isEmpty()) {
            filteredSalleData.setAll(salleData);
        } else {
            String lowerCaseFilter = searchText.toLowerCase();
            List<salle> filteredList = salleData.stream()
                    .filter(salle -> {
                        boolean matchesNom = salle.getNom() != null &&
                                salle.getNom().toLowerCase().contains(lowerCaseFilter);
                        boolean matchesType = salle.getType_salle() != null &&
                                salle.getType_salle().toLowerCase().contains(lowerCaseFilter);
                        boolean matchesStatus = salle.getStatus() != null &&
                                salle.getStatus().toLowerCase().contains(lowerCaseFilter);
                        boolean matchesEtage = salle.getEtage() != null &&
                                String.valueOf(salle.getEtage().getNumero()).contains(lowerCaseFilter);
                        return matchesNom || matchesType || matchesStatus || matchesEtage;
                    })
                    .collect(Collectors.toList());
            filteredSalleData.setAll(filteredList);
        }
    }

    @FXML
    private void handleExportCSV(ActionEvent event) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Exporter les salles en CSV");
        fileChooser.setInitialFileName("salles_export.csv");
        fileChooser.getExtensionFilters().add(
                new FileChooser.ExtensionFilter("Fichiers CSV", "*.csv")
        );

        Stage stage = (Stage) salleTable.getScene().getWindow();
        File file = fileChooser.showSaveDialog(stage);

        if (file != null) {
            try (FileWriter writer = new FileWriter(file)) {
                // Write CSV headers
                writer.append("Nom,Capacité,Type,Status,Priorité,Étage,Image\n");

                // Write data rows
                for (salle s : filteredSalleData) {
                    writer.append(escapeCsvField(s.getNom())).append(",");
                    writer.append(String.valueOf(s.getCapacite())).append(",");
                    writer.append(escapeCsvField(s.getType_salle())).append(",");
                    writer.append(escapeCsvField(s.getStatus())).append(",");
                    writer.append(String.valueOf(s.getPriorite())).append(",");
                    writer.append(s.getEtage() != null ? String.valueOf(s.getEtage().getNumero()) : "").append(",");
                    writer.append(escapeCsvField(s.getImage())).append("\n");
                }

                writer.flush();
                showAlert("Succès", "Les données ont été exportées avec succès dans " + file.getAbsolutePath(), Alert.AlertType.INFORMATION);
            } catch (IOException e) {
                showAlert("Erreur", "Erreur lors de l'exportation CSV: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
    }

    private String escapeCsvField(String field) {
        if (field == null) {
            return "";
        }
        // Escape commas and quotes in the field
        if (field.contains(",") || field.contains("\"")) {
            field = field.replace("\"", "\"\""); // Escape quotes by doubling them
            return "\"" + field + "\""; // Wrap the field in quotes
        }
        return field;
    }

    @FXML
    private void handleBrowseImage(ActionEvent event) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Choisir une image");
        fileChooser.getExtensionFilters().addAll(
                new FileChooser.ExtensionFilter("Images", ".png", ".jpg", ".jpeg", ".gif")
        );

        File selectedFile = fileChooser.showOpenDialog(null);
        if (selectedFile != null) {
            try {
                String fileName = System.currentTimeMillis() + "_" + selectedFile.getName();
                File destFile = new File(IMAGE_DIR + fileName);
                Files.copy(selectedFile.toPath(), destFile.toPath(), StandardCopyOption.REPLACE_EXISTING);

                imagePath = fileName;
                imageField.setText(fileName);
                imagePreview.setImage(new Image(destFile.toURI().toString()));
                imageError.setText("");
            } catch (IOException e) {
                showAlert("Erreur", "Impossible de charger l'image: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
    }

    @FXML
    private void handleSave(ActionEvent event) {
        if (!validateForm()) return;

        salle salle = new salle();
        salle.setNom(nomField.getText());
        salle.setCapacite(Integer.parseInt(capaciteField.getText()));
        salle.setType_salle(typeCombo.getValue());
        salle.setStatus(statusCombo.getValue());
        salle.setPriorite(prioriteSpinner.getValue());
        salle.setEtage(etageCombo.getValue());
        salle.setImage(imagePath);

        salleService.addSalle(salle);
        showAlert("Succès", "Salle ajoutée avec succès", Alert.AlertType.INFORMATION);
        resetForm();
        loadSalles();
    }

    private void showEditDialog(salle salle) {
        // Populate form with salle data
        nomField.setText(salle.getNom());
        capaciteField.setText(String.valueOf(salle.getCapacite()));
        typeCombo.setValue(salle.getType_salle());
        statusCombo.setValue(salle.getStatus());
        prioriteSpinner.getValueFactory().setValue(salle.getPriorite());
        etageCombo.setValue(salle.getEtage());
        imageField.setText(salle.getImage());
        imagePath = salle.getImage();

        // Load image preview
        if (salle.getImage() != null && !salle.getImage().isEmpty()) {
            File imageFile = new File(IMAGE_DIR + salle.getImage());
            if (imageFile.exists()) {
                imagePreview.setImage(new Image(imageFile.toURI().toString()));
            } else {
                imagePreview.setImage(null);
            }
        } else {
            imagePreview.setImage(null);
        }

        // Change save button behavior to update instead of add
        saveBtn.setOnAction(event -> {
            if (!validateForm()) return;

            // Update salle object
            salle.setNom(nomField.getText());
            salle.setCapacite(Integer.parseInt(capaciteField.getText()));
            salle.setType_salle(typeCombo.getValue());
            salle.setStatus(statusCombo.getValue());
            salle.setPriorite(prioriteSpinner.getValue());
            salle.setEtage(etageCombo.getValue());
            salle.setImage(imagePath);

            // Update in database
            salleService.updateSalle(salle);
            showAlert("Succès", "Salle mise à jour avec succès", Alert.AlertType.INFORMATION);
            resetForm();
            loadSalles();

            // Restore default save behavior
            saveBtn.setOnAction(this::handleSave);
        });
    }

    private void confirmAndDelete(salle salle) {
        Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
        alert.setTitle("Confirmer la suppression");
        alert.setHeaderText(null);
        alert.setContentText("Voulez-vous vraiment supprimer la salle " + salle.getNom() + " ?");

        Optional<ButtonType> result = alert.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            salleService.deleteSalle(salle.getId());
            showAlert("Succès", "Salle supprimée avec succès", Alert.AlertType.INFORMATION);
            loadSalles();
        }
    }

    private void showReservationDialog(salle selectedSalle) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/reservationDialog.fxml"));
            DialogPane dialogPane = loader.load();
            ReservationDialogController controller = loader.getController();
            if (controller == null) {
                showAlert("Erreur", "Controller non chargé pour reservationDialog.fxml", Alert.AlertType.ERROR);
                return;
            }
            controller.setSalle(selectedSalle);

            Dialog<ButtonType> dialog = new Dialog<>();
            dialog.setDialogPane(dialogPane);
            dialog.setTitle("Réserver Salle");

            // Pass the dialog to the controller
            controller.setDialog(dialog);

            Optional<ButtonType> result = dialog.showAndWait();
            if (result.isPresent() && result.get() == ButtonType.OK) {
                loadSalles(); // Refresh the TableView
            }
        } catch (IOException e) {
            showAlert("Erreur", "Erreur lors de l'ouverture de la fenêtre de réservation: " + e.getMessage(), Alert.AlertType.ERROR);
        }
    }

    private boolean validateForm() {
        boolean isValid = true;
        clearErrors();

        if (nomField.getText().isEmpty()) {
            nomError.setText("Le nom est obligatoire");
            isValid = false;
        }

        if (capaciteField.getText().isEmpty()) {
            capaciteError.setText("La capacité est obligatoire");
            isValid = false;
        } else {
            try {
                Integer.parseInt(capaciteField.getText());
            } catch (NumberFormatException e) {
                capaciteError.setText("Doit être un nombre valide");
                isValid = false;
            }
        }

        if (typeCombo.getValue() == null) {
            typeError.setText("Le type est obligatoire");
            isValid = false;
        }

        if (statusCombo.getValue() == null) {
            statusError.setText("Le statut est obligatoire");
            isValid = false;
        }

        if (etageCombo.getValue() == null) {
            etageError.setText("L'étage est obligatoire");
            isValid = false;
        }

        return isValid;
    }

    private void clearErrors() {
        nomError.setText("");
        capaciteError.setText("");
        typeError.setText("");
        statusError.setText("");
        prioriteError.setText("");
        etageError.setText("");
        imageError.setText("");
    }

    @FXML
    private void handleClear(ActionEvent event) {
        resetForm();
    }

    private void resetForm() {
        nomField.clear();
        capaciteField.clear();
        typeCombo.getSelectionModel().clearSelection();
        statusCombo.getSelectionModel().clearSelection();
        prioriteSpinner.getValueFactory().setValue(1);
        etageCombo.getSelectionModel().clearSelection();
        imageField.clear();
        imagePreview.setImage(null);
        imagePath = "";
        clearErrors();
    }

    private void showAlert(String title, String message, Alert.AlertType alertType) {
        Alert alert = new Alert(alertType);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    @FXML
    private void showDepartements(ActionEvent event) {
        loadView("/departement.fxml", event);
    }

    @FXML
    private void showReservation(ActionEvent event) {
        loadView("/reservation_list.fxml", event);
    }

    @FXML
    private void showEtages(ActionEvent event) {
        loadView("/etage.fxml", event);
    }

    @FXML
    private void showSalles(ActionEvent event) {
        // Already on salle view
    }

    @FXML
    public void Acceuil(ActionEvent event) {
        loadView("/interface.fxml", event);
    }

    private void loadView(String fxmlPath, ActionEvent event) {
        try {
            Parent root = FXMLLoader.load(getClass().getResource(fxmlPath));
            Stage stage = (Stage) ((Node) event.getSource()).getScene().getWindow();
            stage.setScene(new Scene(root));
            stage.show();
        } catch (IOException e) {
            showAlert("Erreur", "Impossible de charger la vue: " + fxmlPath, Alert.AlertType.ERROR);
        }
    }

    public salle buildSalleFromFields(String nom, String capaciteStr, String type, String status, int priorite, entite.etage etageObj, String image) {

        if (nom == null || nom.trim().isEmpty()) {
            throw new IllegalArgumentException("Le nom est obligatoire");
        }
        
        if (etageObj == null) {
            throw new IllegalArgumentException("L'étage est obligatoire");
        }

        salle s = new salle();
        s.setNom(nom);
        
        try {
            int cap = Integer.parseInt(capaciteStr);
            if (cap <= 0) {
                throw new IllegalArgumentException("La capacité doit être positive");
            }
            s.setCapacite(cap);
        } catch (NumberFormatException e) {
             throw new IllegalArgumentException("Capacité invalide");
        }
        
        s.setType_salle(type);
        s.setStatus(status);
        s.setPriorite(priorite);
        s.setEtage(etageObj);
        s.setImage(image);
        
        return s;
    }
    
}