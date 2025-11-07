package controllers;

import entite.Medicament;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import org.json.JSONArray;
import org.json.JSONObject;
import service.MedicamentService;
import test.MainFx;

import java.time.LocalDate;

public class MedicamentFormController {

    private final MedicamentService medicamentService = new MedicamentService();
    private final MedicamentAPIService apiService = new MedicamentAPIService();

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

        // Ajout d'un gestionnaire d'événement pour la touche Entrée
        medicamentName.setOnAction(event -> handleSearchFromAPI());
    }

    private void configureSpinners() {
        stockSpinner.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 1000, 1));
        prixSpinner.setValueFactory(new SpinnerValueFactory.DoubleSpinnerValueFactory(0.1, 10000.0, 10.0, 0.5));
    }

    private void configureTypeComboBox() {
        typeComboBox.getItems().addAll("Comprimé ", "Capsule", "Sirops", "Poudre" , "Solutions buvables " , "Ampoule" , "Seringue" , "Aérosol" , "Crème" , "Lotion" ,"Suppositoire ");
    }

    @FXML
    private void handleAddMedicament() {
        clearErrors();

        String name = medicamentName.getText().trim();
        String description = medicamentDescription.getText().trim();
        String type = typeComboBox.getValue();
        int stock = stockSpinner.getValue();
        double prix = prixSpinner.getValue();
        LocalDate dateEntree = dateEntreePicker.getValue();
        LocalDate dateExpiration = dateExpirationPicker.getValue();

        if (!validateForm(name, description, type, stock, prix, dateEntree, dateExpiration)) return;

        Medicament m = new Medicament(name, description, type, prix, stock, dateEntree, dateExpiration);
        medicamentService.create(m);
        showAlert("Succès", "Médicament ajouté avec succès !");
        MainFx.loadPage("medicament_list.fxml");
    }

    @FXML
    private void handleBackButton() {
        MainFx.loadPage("DashboardPharmacien.fxml");
    }

    private boolean validateForm(String name, String description, String type,
                                 int stock, double prix, LocalDate dateEntree,
                                 LocalDate dateExpiration) {
        boolean valid = true;

        if (name.isEmpty() || name.length() < 2 || !name.matches("[a-zA-ZÀ-ÿ\\s]+")) {
            nameError.setText("Le nom doit contenir uniquement des lettres (min 2 caractères).");
            valid = false;
        }

        if (description.isEmpty()) {
            descriptionError.setText("La description est requise.");
            valid = false;
        }

        if (type == null || type.isEmpty()) {
            dateError.setText("Le type est requis.");
            valid = false;
        }

        if (stock <= 0) {
            stockError.setText("La quantité en stock doit être supérieure à 0.");
            valid = false;
        }

        if (prix <= 0) {
            prixError.setText("Le prix doit être supérieur à 0.");
            valid = false;
        }

        if (dateEntree == null || dateExpiration == null) {
            dateError.setText("Les deux dates sont requises.");
            valid = false;
        } else if (!dateEntree.isBefore(dateExpiration)) {
            dateError.setText("La date d'entrée doit précéder la date d'expiration.");
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

    @FXML
    public void handleSearchFromAPI() {
        String nomMedicament = medicamentName.getText().trim();
        if (nomMedicament.isEmpty()) {
            showAlert("Erreur", "Veuillez d'abord saisir un nom de médicament.");
            return;
        }

        medicamentDescription.setText("Recherche en cours...");

        // Essayer d'abord la première méthode
        boolean success = processAPISearch(nomMedicament);

        // Si la première méthode échoue, essayer la méthode alternative
        if (!success) {
            medicamentDescription.setText("Premier essai échoué. Tentative alternative...");
            processAlternativeAPISearch(nomMedicament);
        }
    }

    private boolean processAPISearch(String nomMedicament) {
        try {
            // Utilisation du service API
            String responseData = apiService.chercherMedicament(nomMedicament);

            // Vérifier si la réponse contient une erreur
            if (responseData.contains("\"error\":")) {
                JSONObject errorObj = new JSONObject(responseData);
                String errorMessage = errorObj.getString("error");
                System.out.println("Erreur API: " + errorMessage);

                // Ne pas afficher d'alerte ici, on va essayer la méthode alternative
                return false;
            }

            // Analyser et afficher les résultats
            return parseAndDisplayResults(responseData);

        } catch (Exception e) {
            e.printStackTrace();
            medicamentDescription.setText("");
            showAlert("Erreur", "Une erreur s'est produite: " + e.getMessage());
            return false;
        }
    }

    private boolean processAlternativeAPISearch(String nomMedicament) {
        try {
            // Utiliser la méthode alternative simplifiée
            String responseData = apiService.chercherMedicamentSimple(nomMedicament);

            // Vérifier si la réponse contient une erreur
            if (responseData.contains("\"error\":")) {
                JSONObject errorObj = new JSONObject(responseData);
                String errorMessage = errorObj.getString("error");
                medicamentDescription.setText("");
                showAlert("Erreur", "Impossible de trouver des informations: " + errorMessage);
                return false;
            }

            // Analyser et afficher les résultats
            return parseAndDisplayResults(responseData);

        } catch (Exception e) {
            e.printStackTrace();
            medicamentDescription.setText("");
            showAlert("Erreur", "Une erreur s'est produite: " + e.getMessage());
            return false;
        }
    }

    private boolean parseAndDisplayResults(String responseData) {
        try {
            // Analyse JSON
            JSONObject json = new JSONObject(responseData);

            // Vérifier si des résultats ont été trouvés
            if (!json.has("results") || json.getJSONArray("results").length() == 0) {
                medicamentDescription.setText("");
                showAlert("Information", "Aucun médicament trouvé dans la base FDA.");
                return false;
            }

            JSONArray results = json.getJSONArray("results");
            JSONObject medInfo = results.getJSONObject(0);

            // Extraction des informations pour la description
            StringBuilder description = new StringBuilder();

            // Essayer différents champs pour obtenir des informations utiles
            extractField(medInfo, "description", "Description", description);
            extractField(medInfo, "indications_and_usage", "Indications et usage", description);
            extractField(medInfo, "dosage_and_administration", "Dosage et administration", description);
            extractField(medInfo, "purpose", "Objectif", description);
            extractField(medInfo, "warnings", "Avertissements", description);

            // Informations supplémentaires si disponibles dans openfda
            if (medInfo.has("openfda")) {
                JSONObject openfda = medInfo.getJSONObject("openfda");

                extractOpenFDAField(openfda, "generic_name", "Nom générique", description);
                extractOpenFDAField(openfda, "brand_name", "Marque", description);
                extractOpenFDAField(openfda, "manufacturer_name", "Fabricant", description);
                extractOpenFDAField(openfda, "route", "Voie d'administration", description);

                // Mise à jour du type de médicament
                if (openfda.has("dosage_form")) {
                    try {
                        JSONArray dosageArray = openfda.getJSONArray("dosage_form");
                        if (dosageArray.length() > 0) {
                            String dosageForm = dosageArray.getString(0);
                            setClosestType(dosageForm);
                            description.append("\nForme: ").append(dosageForm);
                        }
                    } catch (Exception e) {
                        // Ignorer cette erreur spécifique
                    }
                }
            }

            // Si aucune information utile n'a été trouvée
            if (description.length() == 0) {
                description.append("Médicament trouvé dans la base FDA, mais sans description détaillée disponible.");
            }

            // Afficher la description
            medicamentDescription.setText(description.toString());

            // Notification de succès
            showAlert("Succès", "Informations chargées depuis l'API FDA !");
            return true;

        } catch (Exception e) {
            e.printStackTrace();
            medicamentDescription.setText("");
            showAlert("Erreur", "Erreur lors de l'analyse des données: " + e.getMessage());
            return false;
        }
    }

    private void extractField(JSONObject json, String fieldName, String displayName, StringBuilder builder) {
        if (json.has(fieldName)) {
            try {
                Object field = json.get(fieldName);
                String value;

                if (field instanceof JSONArray) {
                    JSONArray array = (JSONArray) field;
                    if (array.length() > 0) {
                        value = array.getString(0);
                    } else {
                        return;
                    }
                } else {
                    value = field.toString();
                }

                // Limiter la longueur du texte pour éviter des descriptions trop longues
                if (value.length() > 200) {
                    value = value.substring(0, 197) + "...";
                }

                if (builder.length() > 0) {
                    builder.append("\n\n");
                }

                builder.append(displayName).append(": ").append(value);
            } catch (Exception e) {
                // Ignorer les erreurs lors de l'extraction
            }
        }
    }

    private void extractOpenFDAField(JSONObject openfda, String fieldName, String displayName, StringBuilder builder) {
        if (openfda.has(fieldName)) {
            try {
                JSONArray array = openfda.getJSONArray(fieldName);
                if (array.length() > 0) {
                    if (builder.length() > 0) {
                        builder.append("\n");
                    }
                    builder.append(displayName).append(": ").append(array.getString(0));
                }
            } catch (Exception e) {
                // Ignorer les erreurs lors de l'extraction
            }
        }
    }

    // Méthode pour trouver le type de médicament le plus proche dans la liste
    private void setClosestType(String apiDosageForm) {
        // Conversion en minuscule pour faciliter la comparaison
        String dosageFormLower = apiDosageForm.toLowerCase();

        // Correspondances possibles
        if (dosageFormLower.contains("tablet") || dosageFormLower.contains("comprimé")) {
            typeComboBox.setValue("Comprimé");
        } else if (dosageFormLower.contains("capsule")) {
            typeComboBox.setValue("Capsule");
        } else if (dosageFormLower.contains("syrup") || dosageFormLower.contains("sirop")) {
            typeComboBox.setValue("Sirops");
        } else if (dosageFormLower.contains("powder") || dosageFormLower.contains("poudre")) {
            typeComboBox.setValue("Poudre");
        } else if (dosageFormLower.contains("solution") || dosageFormLower.contains("liquid")) {
            typeComboBox.setValue("Solutions buvables");
        } else if (dosageFormLower.contains("ampule") || dosageFormLower.contains("ampoule")) {
            typeComboBox.setValue("Ampoule");
        } else if (dosageFormLower.contains("injection") || dosageFormLower.contains("syringe")) {
            typeComboBox.setValue("Seringue");
        } else if (dosageFormLower.contains("aerosol") || dosageFormLower.contains("spray")) {
            typeComboBox.setValue("Aérosol");
        } else if (dosageFormLower.contains("cream") || dosageFormLower.contains("crème")) {
            typeComboBox.setValue("Crème");
        } else if (dosageFormLower.contains("lotion")) {
            typeComboBox.setValue("Lotion");
        } else if (dosageFormLower.contains("suppository")) {
            typeComboBox.setValue("Suppositoire");
        }
    }
    @FXML
    private void openChatbot() {
        MainFx.loadPage("chatbot_medicament.fxml");
    }
}