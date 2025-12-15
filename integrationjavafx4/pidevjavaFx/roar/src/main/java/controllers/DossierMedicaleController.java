package controllers;

import entite.DossierMedicale;
import entite.Sejour;
import entite.User;
import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import service.DossierMedicaleService;
import service.SejourService;
import service.UserServiceE;
import util.AlertUtil;
import util.DossierMedicaleValidator;
import util.ImageUploadUtil;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;

public class DossierMedicaleController implements Initializable {
    
    @FXML
    private TableView<DossierMedicale> dossierTable;
    
    @FXML
    private TableColumn<DossierMedicale, Integer> colId;
    
    @FXML
    private TableColumn<DossierMedicale, String> colDateCreation;
    
    @FXML
    private TableColumn<DossierMedicale, String> colPatient;
    
    @FXML
    private TableColumn<DossierMedicale, String> colMedecin;
    
    @FXML
    private TableColumn<DossierMedicale, String> colStatut;
    
    @FXML
    private Button btnAjouter;
    
    @FXML
    private Button btnModifier;
    
    @FXML
    private Button btnSupprimer;
    
    @FXML
    private Button btnVoir;
    
    @FXML
    private DatePicker dateCreationPicker;
    
    @FXML
    private TextArea txtHistoriqueMaladies;
    
    @FXML
    private TextArea txtOperationsPassees;
    
    @FXML
    private TextArea txtConsultationsPassees;
    
    @FXML
    private ComboBox<String> comboStatutDossier;
    
    @FXML
    private TextArea txtNotes;
    
    @FXML
    private ComboBox<User> comboPatient;
    
    @FXML
    private ComboBox<User> comboMedecin;
    
    @FXML
    private Button btnChooseImage;
    
    @FXML
    private ImageView imagePreview;
    
    @FXML
    private TableView<Sejour> sejourTable;
    
    @FXML
    private TableColumn<Sejour, String> colDateEntree;
    
    @FXML
    private TableColumn<Sejour, String> colDateSortie;
    
    @FXML
    private TableColumn<Sejour, String> colTypeSejour;
    
    @FXML
    private TableColumn<Sejour, Double> colFraisSejour;
    
    @FXML
    private TableColumn<Sejour, String> colStatutPaiement;
    
    @FXML
    private Label lblImagePath;
    
    @FXML
    private Label lblValidationError;
    
    private DossierMedicaleService dossierService;
    private SejourService sejourService;
    private UserServiceE userServiceE;
    
    private ObservableList<DossierMedicale> dossierList;
    private ObservableList<Sejour> sejourList;
    
    private DossierMedicale currentDossier;
    private File selectedImageFile;
    private String currentImageFilename;
    
    private static final DateTimeFormatter DATE_FORMATTER = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");
    private static final String[] STATUT_OPTIONS = {"Actif", "Archivé", "En attente"};
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // Initialize services
        dossierService = new DossierMedicaleService();
        sejourService = new SejourService();
        userServiceE = new UserServiceE();
        
        // Set up circular references
        dossierService.setSejourService(sejourService);
        sejourService.setDossierService(dossierService);
        
        // Initialize lists
        dossierList = FXCollections.observableArrayList();
        sejourList = FXCollections.observableArrayList();
        
        // Set up dossier table columns
        colId.setCellValueFactory(new PropertyValueFactory<>("id"));
        colDateCreation.setCellValueFactory(cellData -> {
            DossierMedicale dossier = cellData.getValue();
            LocalDateTime date = dossier.getDateDeCreation();
            return new SimpleStringProperty(date != null ? date.format(DATE_FORMATTER) : "");
        });
        colPatient.setCellValueFactory(cellData -> {
            DossierMedicale dossier = cellData.getValue();
            User patient = dossier.getPatient();
            return new SimpleStringProperty(patient != null ? patient.getPrenom() + " " + patient.getNom() : "");
        });
        colMedecin.setCellValueFactory(cellData -> {
            DossierMedicale dossier = cellData.getValue();
            User medecin = dossier.getMedecin();
            return new SimpleStringProperty(medecin != null ? medecin.getPrenom() + " " + medecin.getNom() : "");
        });
        colStatut.setCellValueFactory(new PropertyValueFactory<>("statutDossier"));
        
        // Set up séjour table columns
        colDateEntree.setCellValueFactory(cellData -> {
            Sejour sejour = cellData.getValue();
            LocalDateTime date = sejour.getDateEntree();
            return new SimpleStringProperty(date != null ? date.format(DATE_FORMATTER) : "");
        });
        colDateSortie.setCellValueFactory(cellData -> {
            Sejour sejour = cellData.getValue();
            LocalDateTime date = sejour.getDateSortie();
            return new SimpleStringProperty(date != null ? date.format(DATE_FORMATTER) : "");
        });
        colTypeSejour.setCellValueFactory(new PropertyValueFactory<>("typeSejour"));
        colFraisSejour.setCellValueFactory(new PropertyValueFactory<>("fraisSejour"));
        colStatutPaiement.setCellValueFactory(new PropertyValueFactory<>("statutPaiement"));
        
        // Important: set the items for the sejour table
        sejourTable.setItems(sejourList);
        dossierTable.setItems(dossierList);
        
        // Set up status options
        comboStatutDossier.setItems(FXCollections.observableArrayList(STATUT_OPTIONS));
        
        // Initialize text formatters for input validation
        initializeTextFormatters();
        
        // Load users for combo boxes
        loadUsers();
        
        // Load dossiers
        loadDossiers();
        
        // Add selection listener to the dossier table
        dossierTable.getSelectionModel().selectedItemProperty().addListener((obs, oldSelection, newSelection) -> {
            if (newSelection != null) {
                currentDossier = newSelection;
                loadSejoursForCurrentDossier();
                displayDossierDetails(newSelection);
                enableDossierButtons(true);
            } else {
                currentDossier = null;
                sejourList.clear();
                clearDossierForm();
                enableDossierButtons(false);
            }
        });
        
        // Initialize buttons as disabled
        enableDossierButtons(false);
    }
    
    private void initializeTextFormatters() {
        // Formatter pour les notes (limite à 500 caractères et caractères autorisés)
        TextFormatter<String> notesFormatter = new TextFormatter<>(change -> {
            String newText = change.getControlNewText();
            if (newText.length() <= 500 && newText.matches("^[\\p{L}\\p{N}\\p{P}\\p{Z}\\s]*$")) {
                return change;
            }
            return null;
        });
        txtNotes.setTextFormatter(notesFormatter);

        // Ajouter un listener pour la validation en temps réel
        txtNotes.textProperty().addListener((obs, oldVal, newVal) -> {
            if (newVal != null) {
                if (newVal.length() > 500) {
                    txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                    lblValidationError.setText("❌ Les notes ne peuvent pas dépasser 500 caractères");
                    lblValidationError.setVisible(true);
                } else if (newVal.contains("<script>") || newVal.contains("javascript:")) {
                    txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                    lblValidationError.setText("❌ Les notes contiennent du code malveillant");
                    lblValidationError.setVisible(true);
                } else if (!newVal.matches("^[\\p{L}\\p{N}\\p{P}\\p{Z}\\s]*$")) {
                    txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                    lblValidationError.setText("❌ Les notes contiennent des caractères non autorisés");
                    lblValidationError.setVisible(true);
                } else {
                    txtNotes.setStyle("");
                    lblValidationError.setVisible(false);
                }
            }
        });

        // Formatter pour l'historique des maladies (limite à 1000 caractères)
        TextFormatter<String> historiqueFormatter = new TextFormatter<>(change -> {
            String newText = change.getControlNewText();
            if (newText.length() <= 1000) {
                return change;
            }
            return null;
        });
        txtHistoriqueMaladies.setTextFormatter(historiqueFormatter);

        // Formatter pour les opérations passées (limite à 1000 caractères)
        TextFormatter<String> operationsFormatter = new TextFormatter<>(change -> {
            String newText = change.getControlNewText();
            if (newText.length() <= 1000) {
                return change;
            }
            return null;
        });
        txtOperationsPassees.setTextFormatter(operationsFormatter);

        // Formatter pour les consultations passées (limite à 1000 caractères)
        TextFormatter<String> consultationsFormatter = new TextFormatter<>(change -> {
            String newText = change.getControlNewText();
            if (newText.length() <= 1000) {
                return change;
            }
            return null;
        });
        txtConsultationsPassees.setTextFormatter(consultationsFormatter);
    }
    
    private void loadUsers() {
        // Debug: Get ALL users to check their types
        List<User> allUsers = userServiceE.recupererTousUsers();
        System.out.println("Total users in database: " + allUsers.size());
        System.out.println("User types in database:");
        
        // Count users by type
        for (User user : allUsers) {
            System.out.println("User ID: " + user.getId() + 
                             ", Name: " + user.getPrenom() + " " + user.getNom() + 
                             ", Type: " + user.getType() +
                             ", Specialite: " + user.getSpecialite() +
                             ", IsMedecin: " + user.isMedecin());
        }
        
        // Load patients using the type field
        List<User> patients = userServiceE.recupererUsersParRole("patient");
        System.out.println("Retrieved " + patients.size() + " patients from database");
        comboPatient.setItems(FXCollections.observableArrayList(patients));
        
        // Load doctors - try both spellings
        List<User> medecins = new ArrayList<>();
        
        // Try with "medecin"
        List<User> medecins1 = userServiceE.recupererUsersParRole("medecin");
        System.out.println("Found " + medecins1.size() + " doctors with type 'medecin'");
        medecins.addAll(medecins1);
        
        // Try with "medcin"
        List<User> medecins2 = userServiceE.recupererUsersParRole("medcin");
        System.out.println("Found " + medecins2.size() + " doctors with type 'medcin'");
        medecins.addAll(medecins2);
        
        // If still no doctors found, look for users with specialite
        if (medecins.isEmpty()) {
            System.out.println("No doctors found by type, looking for users with specialite");
            for (User user : allUsers) {
                if (user.getSpecialite() != null && !user.getSpecialite().isEmpty() &&
                    !user.getType().equals("patient")) {
                    System.out.println("Found potential doctor: " + user.getPrenom() + " " + user.getNom() + 
                                     ", Type: " + user.getType() + 
                                     ", Specialite: " + user.getSpecialite());
                    medecins.add(user);
                }
            }
        }
        
        System.out.println("Total doctors found: " + medecins.size());
        comboMedecin.setItems(FXCollections.observableArrayList(medecins));
        
        // Setup string converters for both combo boxes to display user names
        javafx.util.StringConverter<User> userStringConverter = new javafx.util.StringConverter<User>() {
            @Override
            public String toString(User user) {
                if (user == null) return "";
                return user.getPrenom() + " " + user.getNom() + 
                       (user.getSpecialite() != null ? " (" + user.getSpecialite() + ")" : "");
            }

            @Override
            public User fromString(String string) {
                // This is not needed for our use case
                return null;
            }
        };
        
        comboPatient.setConverter(userStringConverter);
        comboMedecin.setConverter(userStringConverter);
    }
    
    private void loadDossiers() {
        try {
            List<DossierMedicale> dossiers = dossierService.recupererTousDossiers();
            if (dossiers != null) {
                System.out.println("Loaded " + dossiers.size() + " dossiers");
                dossierList.clear();
                dossierList.addAll(dossiers);
                dossierTable.refresh();
            } else {
                System.out.println("No dossiers loaded - returned null list");
                dossierList.clear();
            }
        } catch (Exception e) {
            System.err.println("Error loading dossiers: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    private void loadSejoursForCurrentDossier() {
        sejourList.clear();  // Always clear the list first
        
        if (currentDossier != null) {
            try {
                // Set the items again to be safe
                sejourTable.setItems(sejourList);
                
                List<Sejour> sejours = sejourService.recupererSejoursParDossier(currentDossier.getId());
                System.out.println("Loading sejours for dossier ID: " + currentDossier.getId() + 
                                   " - Found: " + (sejours != null ? sejours.size() : 0));
                
                if (sejours != null && !sejours.isEmpty()) {
                    sejourList.addAll(sejours);
                    System.out.println("Added " + sejours.size() + " sejours to the observable list");
                }
                
                // Force a refresh
                sejourTable.refresh();
            } catch (Exception e) {
                System.err.println("Error loading sejours for dossier: " + e.getMessage());
                e.printStackTrace();
            }
        }
    }
    
    private void displayDossierDetails(DossierMedicale dossier) {
        if (dossier == null) {
            clearDossierForm();
            return;
        }
        
        LocalDateTime dateCreation = dossier.getDateDeCreation();
        // TODO: Set date picker value when implemented
        
        txtHistoriqueMaladies.setText(dossier.getHistoriqueDesMaladies());
        txtOperationsPassees.setText(dossier.getOperationsPassees());
        txtConsultationsPassees.setText(dossier.getConsultationsPassees());
        comboStatutDossier.setValue(dossier.getStatutDossier());
        txtNotes.setText(dossier.getNotes());
        comboPatient.setValue(dossier.getPatient());
        comboMedecin.setValue(dossier.getMedecin());
        
        // Display image if available
        currentImageFilename = dossier.getImage();
        displayImage(currentImageFilename);
    }
    
    private void clearDossierForm() {
        dateCreationPicker.setValue(null);
        txtHistoriqueMaladies.clear();
        txtOperationsPassees.clear();
        txtConsultationsPassees.clear();
        comboStatutDossier.setValue(null);
        txtNotes.clear();
        comboPatient.setValue(null);
        comboMedecin.setValue(null);
        imagePreview.setImage(null);
        currentImageFilename = null;
        selectedImageFile = null;
    }
    
    private void enableDossierButtons(boolean enable) {
        btnModifier.setDisable(!enable);
        btnSupprimer.setDisable(!enable);
        btnVoir.setDisable(!enable);
    }
    
    private void displayImage(String filename) {
        if (filename != null && !filename.isEmpty() && ImageUploadUtil.imageExists(filename)) {
            String imagePath = ImageUploadUtil.getImagePath(filename);
            if (imagePath != null) {
                try {
                    Image image = new Image(new File(imagePath).toURI().toString());
                    imagePreview.setImage(image);
                    imagePreview.setPreserveRatio(true);
                    imagePreview.setFitWidth(200);
                } catch (Exception e) {
                    System.err.println("Error loading image: " + e.getMessage());
                    imagePreview.setImage(null);
                }
            }
        } else {
            imagePreview.setImage(null);
        }
    }
    
    @FXML
    private void handleChooseImage(ActionEvent event) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Sélectionner une image");
        fileChooser.getExtensionFilters().addAll(
                new FileChooser.ExtensionFilter("Images", "*.png", "*.jpg", "*.jpeg", "*.gif")
        );
        
        Window owner = ((Node) event.getSource()).getScene().getWindow();
        selectedImageFile = fileChooser.showOpenDialog(owner);
        
        if (selectedImageFile != null) {
            try {
                Image image = new Image(selectedImageFile.toURI().toString());
                imagePreview.setImage(image);
                imagePreview.setPreserveRatio(true);
                imagePreview.setFitWidth(200);
            } catch (Exception e) {
                AlertUtil.showError(owner, "Erreur", "Impossible de charger l'image sélectionnée.");
            }
        }
    }
    
    @FXML
    private void handleAjouter(ActionEvent event) {
        // Réinitialiser les styles et messages
        comboPatient.setStyle("");
        comboMedecin.setStyle("");
        comboStatutDossier.setStyle("");
        lblValidationError.setText("");
        lblValidationError.setVisible(false);

        // Vérification initiale des champs obligatoires
        if (!validateRequiredFields()) {
            return; // Arrêter si la validation échoue
        }

        try {
            // Créer le dossier seulement si la validation est passée
            DossierMedicale dossier = createDossier();
            if (dossier == null) {
                return; // Arrêter si la création du dossier échoue
            }

            // Validation supplémentaire avec DossierMedicaleValidator
            DossierMedicaleValidator.ValidationResult validationResult = DossierMedicaleValidator.validate(dossier);
            if (!validationResult.isValid()) {
                lblValidationError.setText(validationResult.getErrorMessage());
                lblValidationError.setVisible(true);
                AlertUtil.showError(null, "Erreur de validation", validationResult.getErrorMessage());
                return;
            }

            // Sauvegarder le dossier
            boolean success = dossierService.ajouterDossier(dossier);
            if (success) {
                AlertUtil.showInformation(null, "Succès", "Le dossier médical a été créé avec succès.");
                loadDossiers();
                clearDossierForm();
            } else {
                AlertUtil.showError(null, "Erreur", "Une erreur s'est produite lors de la création du dossier médical.");
            }
        } catch (Exception e) {
            System.err.println("Error in handleAjouter: " + e.getMessage());
            e.printStackTrace();
            AlertUtil.showError(null, "Erreur", "Une erreur s'est produite lors de la création du dossier médical: " + e.getMessage());
        }
    }

    private boolean validateRequiredFields() {
        boolean isValid = true;
        StringBuilder errorMessage = new StringBuilder();

        // Vérification du patient
        if (comboPatient.getValue() == null) {
            errorMessage.append("❌ Le patient est obligatoire\n");
            comboPatient.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            comboPatient.setStyle("");
        }

        // Vérification du médecin
        if (comboMedecin.getValue() == null) {
            errorMessage.append("❌ Le médecin est obligatoire\n");
            comboMedecin.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            comboMedecin.setStyle("");
        }

        // Vérification du statut
        if (comboStatutDossier.getValue() == null || comboStatutDossier.getValue().trim().isEmpty()) {
            errorMessage.append("❌ Le statut du dossier est obligatoire\n");
            comboStatutDossier.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            comboStatutDossier.setStyle("");
        }

        // Vérification de l'historique des maladies
        String historique = txtHistoriqueMaladies.getText();
        if (historique == null || historique.trim().isEmpty()) {
            errorMessage.append("❌ L'historique des maladies est obligatoire\n");
            txtHistoriqueMaladies.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else if (historique.length() > 1000) {
            errorMessage.append("❌ L'historique des maladies ne peut pas dépasser 1000 caractères\n");
            txtHistoriqueMaladies.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            txtHistoriqueMaladies.setStyle("");
        }

        // Vérification des opérations passées
        String operations = txtOperationsPassees.getText();
        if (operations == null || operations.trim().isEmpty()) {
            errorMessage.append("❌ Les opérations passées sont obligatoires\n");
            txtOperationsPassees.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else if (operations.length() > 1000) {
            errorMessage.append("❌ Les opérations passées ne peuvent pas dépasser 1000 caractères\n");
            txtOperationsPassees.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            txtOperationsPassees.setStyle("");
        }

        // Vérification des consultations passées
        String consultations = txtConsultationsPassees.getText();
        if (consultations == null || consultations.trim().isEmpty()) {
            errorMessage.append("❌ Les consultations passées sont obligatoires\n");
            txtConsultationsPassees.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else if (consultations.length() > 1000) {
            errorMessage.append("❌ Les consultations passées ne peuvent pas dépasser 1000 caractères\n");
            txtConsultationsPassees.setStyle("-fx-border-color: red; -fx-border-width: 2;");
            isValid = false;
        } else {
            txtConsultationsPassees.setStyle("");
        }

        // Vérification des notes
        String notes = txtNotes.getText();
        if (notes != null) {
            notes = notes.trim();
            if (notes.length() > 500) {
                errorMessage.append("❌ Les notes ne peuvent pas dépasser 500 caractères\n");
                txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                isValid = false;
            } else if (notes.contains("<script>") || notes.contains("javascript:")) {
                errorMessage.append("❌ Les notes contiennent du code malveillant\n");
                txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                isValid = false;
            } else if (!notes.matches("^[\\p{L}\\p{N}\\p{P}\\p{Z}\\s]*$")) {
                errorMessage.append("❌ Les notes contiennent des caractères non autorisés\n");
                txtNotes.setStyle("-fx-border-color: red; -fx-border-width: 2;");
                isValid = false;
            } else {
                txtNotes.setStyle("");
            }
        }

        if (!isValid) {
            // Afficher les messages d'erreur
            lblValidationError.setText(errorMessage.toString());
            lblValidationError.setStyle("-fx-text-fill: red; -fx-font-weight: bold; -fx-font-size: 14px; -fx-padding: 10;");
            lblValidationError.setVisible(true);

            // Afficher une alerte
            Alert alert = new Alert(Alert.AlertType.ERROR);
            alert.setTitle("Erreur de validation");
            alert.setHeaderText("Champs obligatoires manquants");
            alert.setContentText("Veuillez remplir tous les champs obligatoires avant de créer le dossier.");
            alert.showAndWait();
        }

        return isValid;
    }

    private DossierMedicale createDossier() {
        // Vérification finale avant la création
        if (comboPatient.getValue() == null || comboMedecin.getValue() == null || 
            comboStatutDossier.getValue() == null || comboStatutDossier.getValue().trim().isEmpty()) {
            AlertUtil.showError(null, "Erreur", "Les données du dossier sont invalides. Veuillez remplir tous les champs obligatoires.");
            return null;
        }

        try {
            DossierMedicale dossier = new DossierMedicale();
            dossier.setDateDeCreation(LocalDateTime.now());
            dossier.setHistoriqueDesMaladies(txtHistoriqueMaladies.getText());
            dossier.setOperationsPassees(txtOperationsPassees.getText());
            dossier.setConsultationsPassees(txtConsultationsPassees.getText());
            dossier.setStatutDossier(comboStatutDossier.getValue());
            dossier.setNotes(txtNotes.getText());
            dossier.setPatient(comboPatient.getValue());
            dossier.setMedecin(comboMedecin.getValue());

            // Gestion de l'image
            if (selectedImageFile != null) {
                String newFilename = ImageUploadUtil.saveImage(selectedImageFile, selectedImageFile.getName());
                if (newFilename != null) {
                    dossier.setImage(newFilename);
                }
            }

            return dossier;
        } catch (Exception e) {
            System.err.println("Error creating dossier: " + e.getMessage());
            e.printStackTrace();
            AlertUtil.showError(null, "Erreur", "Erreur lors de la création du dossier: " + e.getMessage());
            return null;
        }
    }
    
    @FXML
    private void handleModifier(ActionEvent event) {
        if (currentDossier == null) {
            AlertUtil.showError(null, "Erreur", "Veuillez sélectionner un dossier à modifier.");
            return;
        }
        
        // Update dossier
        currentDossier.setHistoriqueDesMaladies(txtHistoriqueMaladies.getText());
        currentDossier.setOperationsPassees(txtOperationsPassees.getText());
        currentDossier.setConsultationsPassees(txtConsultationsPassees.getText());
        currentDossier.setStatutDossier(comboStatutDossier.getValue());
        currentDossier.setNotes(txtNotes.getText());
        currentDossier.setPatient(comboPatient.getValue());
        currentDossier.setMedecin(comboMedecin.getValue());
        
        // Handle image upload
        if (selectedImageFile != null) {
            String newFilename = ImageUploadUtil.saveImage(selectedImageFile, selectedImageFile.getName());
            if (newFilename != null) {
                // Delete old image if exists
                if (currentImageFilename != null && !currentImageFilename.isEmpty()) {
                    ImageUploadUtil.deleteImage(currentImageFilename);
                }
                currentDossier.setImage(newFilename);
            }
        }
        
        // Validate dossier
        DossierMedicaleValidator.ValidationResult validationResult = DossierMedicaleValidator.validate(currentDossier);
        if (!validationResult.isValid()) {
            lblValidationError.setText(validationResult.getErrorMessage());
            lblValidationError.setVisible(true);
            return;
        }
        
        // Save dossier
        boolean success = dossierService.modifierDossier(currentDossier);
        
        if (success) {
            AlertUtil.showInformation(null, "Succès", "Le dossier médical a été mis à jour avec succès.");
            loadDossiers();
            lblValidationError.setVisible(false);
        } else {
            AlertUtil.showError(null, "Erreur", "Une erreur s'est produite lors de la mise à jour du dossier médical.");
        }
    }
    
    @FXML
    private void handleSupprimer(ActionEvent event) {
        Window owner = ((Node) event.getSource()).getScene().getWindow();
        
        if (currentDossier == null) {
            AlertUtil.showError(owner, "Erreur", "Veuillez sélectionner un dossier à supprimer.");
            return;
        }
        
        boolean confirm = AlertUtil.showConfirmation(owner, "Confirmation", 
                "Êtes-vous sûr de vouloir supprimer ce dossier médical ? Cette action est irréversible.");
        
        if (!confirm) {
            return;
        }
        
        // Delete image if exists
        if (currentDossier.getImage() != null && !currentDossier.getImage().isEmpty()) {
            ImageUploadUtil.deleteImage(currentDossier.getImage());
        }
        
        // Delete dossier
        boolean success = dossierService.supprimerDossier(currentDossier.getId());
        
        if (success) {
            AlertUtil.showInformation(owner, "Succès", "Le dossier médical a été supprimé avec succès.");
            loadDossiers();
            clearDossierForm();
        } else {
            AlertUtil.showError(owner, "Erreur", "Une erreur s'est produite lors de la suppression du dossier médical.");
        }
    }
    
    @FXML
    private void handleVoir(ActionEvent event) {
        if (currentDossier == null) {
            AlertUtil.showError(((Node) event.getSource()).getScene().getWindow(), 
                    "Erreur", "Veuillez sélectionner un dossier à visualiser.");
            return;
        }
        
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/dossier_detail.fxml"));
            Parent root = loader.load();
            
            DossierDetailController controller = loader.getController();
            controller.setDossier(currentDossier);
            
            Stage stage = new Stage();
            stage.setTitle("Détails du Dossier Médical #" + currentDossier.getId());
            stage.setScene(new Scene(root));
            stage.initModality(Modality.WINDOW_MODAL);
            stage.initOwner(((Node) event.getSource()).getScene().getWindow());
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            AlertUtil.showError(((Node) event.getSource()).getScene().getWindow(), 
                    "Erreur", "Impossible d'ouvrir la vue détaillée du dossier.");
        }
    }
    
    @FXML
    private void handleAjouterSejour(ActionEvent event) {
        if (currentDossier == null) {
            AlertUtil.showError(((Node) event.getSource()).getScene().getWindow(), 
                    "Erreur", "Veuillez d'abord sélectionner un dossier médical.");
            return;
        }
        
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/sejour_form.fxml"));
            Parent root = loader.load();
            
            SejourController controller = loader.getController();
            controller.initNewSejour(currentDossier);
            
            Stage stage = new Stage();
            stage.setTitle("Ajouter un Séjour");
            stage.setScene(new Scene(root));
            stage.initModality(Modality.WINDOW_MODAL);
            stage.initOwner(((Node) event.getSource()).getScene().getWindow());
            stage.setOnHidden(e -> loadSejoursForCurrentDossier());
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            AlertUtil.showError(((Node) event.getSource()).getScene().getWindow(), 
                    "Erreur", "Impossible d'ouvrir le formulaire de séjour.");
        }
    }
    
    @FXML
    private void handleRefresh(ActionEvent event) {
        loadDossiers();
        clearDossierForm();
    }
    
    @FXML
    private void handleBackToHome(ActionEvent event) {
        try {
            // Load the interface.fxml
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/interface.fxml"));
            Parent root = loader.load();
            
            // Get the current stage
            Stage stage = (Stage) ((Node) event.getSource()).getScene().getWindow();
            
            // Set the scene
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.setTitle("Admin Dashboard");
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            AlertUtil.showError(null, "Erreur", "Erreur lors du retour à l'interface principale\n" + e.getMessage());
        }
    }
    
    /**
     * Launch the QR code scanner
     */
    @FXML
    private void handleOpenQRScanner(ActionEvent event) {
        try {
            // Load the QR code scanner FXML
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/qr_code_scanner.fxml"));
            Parent root = loader.load();
            
            // Create and configure the stage
            Stage qrScannerStage = new Stage();
            qrScannerStage.setTitle("Scanner de Code QR - Dossier Médical");
            qrScannerStage.setScene(new Scene(root));
            qrScannerStage.initModality(Modality.APPLICATION_MODAL);
            
            // Show the QR code scanner
            qrScannerStage.show();
            
        } catch (IOException e) {
            AlertUtil.showError(null, "Erreur", "Erreur lors de l'ouverture du scanner de code QR: " + e.getMessage());
        }
    }
} 