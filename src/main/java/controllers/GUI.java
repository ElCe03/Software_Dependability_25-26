package controllers;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.stream.Collectors;
import javafx.event.ActionEvent;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;
import java.io.IOException;

public class GUI {
    // Symptom Inputs
    @FXML private ComboBox<String> feverCombo, coughCombo, fatigueCombo, breathingCombo;
    @FXML private ComboBox<String> ageCombo, genderCombo, bpCombo, cholesterolCombo;

    // Results Display
    @FXML private Label result;
    @FXML private TableView<Prediction> historyTable;
    @FXML private TableColumn<Prediction, String> timeColumn;
    @FXML private TableColumn<Prediction, String> diseaseColumn;
    @FXML private TableColumn<Prediction, Double> confidenceColumn;
    @FXML private TableColumn<Prediction, String> symptomsColumn;
    @FXML private Button calculateButton;

    private Core core = new Core();
    private ObservableList<Prediction> predictionHistory = FXCollections.observableArrayList();

    public static class Prediction {
        private final String time;
        private final String disease;
        private final double confidence;
        private final String symptoms;

        public Prediction(String time, String disease, double confidence, String symptoms) {
            this.time = time;
            this.disease = disease;
            this.confidence = confidence;
            this.symptoms = symptoms;
        }

        public String getTime() { return time; }
        public String getDisease() { return disease; }
        public double getConfidence() { return confidence; }
        public String getSymptoms() { return symptoms; }
    }

    @FXML
    private void initialize() {
        // Setup symptom combo boxes
        ObservableList<String> yesNoOptions = FXCollections.observableArrayList("Yes", "No", "Unknown");
        feverCombo.setItems(yesNoOptions);
        feverCombo.setPromptText("Fever");
        coughCombo.setItems(yesNoOptions);
        coughCombo.setPromptText("Cough");
        fatigueCombo.setItems(yesNoOptions);
        fatigueCombo.setPromptText("Fatigue");
        breathingCombo.setItems(yesNoOptions);
        breathingCombo.setPromptText("Breathing Difficulty");

        // Setup patient profile inputs
        ObservableList<String> ageGroups = FXCollections.observableArrayList(
                "Under 20", "20-29", "30-39", "40-49", "50-59", "60-69", "70+");
        ageCombo.setItems(ageGroups);
        ageCombo.setPromptText("Age Group");

        ObservableList<String> genders = FXCollections.observableArrayList("Male", "Female", "Other");
        genderCombo.setItems(genders);
        genderCombo.setPromptText("Gender");

        ObservableList<String> bpLevels = FXCollections.observableArrayList(
                "Normal", "Elevated", "High", "Very High");
        bpCombo.setItems(bpLevels);
        bpCombo.setPromptText("Blood Pressure");

        ObservableList<String> cholesterolLevels = FXCollections.observableArrayList(
                "Normal", "Borderline High", "High", "Very High");
        cholesterolCombo.setItems(cholesterolLevels);
        cholesterolCombo.setPromptText("Cholesterol Level");

        // Setup TableView
        timeColumn.setCellValueFactory(new PropertyValueFactory<>("time"));
        diseaseColumn.setCellValueFactory(new PropertyValueFactory<>("disease"));
        confidenceColumn.setCellValueFactory(new PropertyValueFactory<>("confidence"));
        symptomsColumn.setCellValueFactory(new PropertyValueFactory<>("symptoms"));
        historyTable.setItems(predictionHistory);

        // Style button
        calculateButton.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white; -fx-font-weight: bold;");
    }

    @FXML
    private void calculate() {
        try {
            Map<String, String> inputSymptoms = new HashMap<>();

            // Collect all symptom inputs
            if (feverCombo.getValue() != null)
                inputSymptoms.put("Fever", feverCombo.getValue());
            if (coughCombo.getValue() != null)
                inputSymptoms.put("Cough", coughCombo.getValue());
            if (fatigueCombo.getValue() != null)
                inputSymptoms.put("Fatigue", fatigueCombo.getValue());
            if (breathingCombo.getValue() != null)
                inputSymptoms.put("Difficulty Breathing", breathingCombo.getValue());
            if (ageCombo.getValue() != null)
                inputSymptoms.put("Age", ageCombo.getValue());
            if (genderCombo.getValue() != null)
                inputSymptoms.put("Gender", genderCombo.getValue());
            if (bpCombo.getValue() != null)
                inputSymptoms.put("Blood Pressure", bpCombo.getValue());
            if (cholesterolCombo.getValue() != null)
                inputSymptoms.put("Cholesterol Level", cholesterolCombo.getValue());

            if (inputSymptoms.isEmpty()) {
                showError("Please select at least one symptom");
                return;
            }

            Map<String, Double> probabilities = core.predict(inputSymptoms);

            if (probabilities.isEmpty()) {
                showError("No matching diseases found for these symptoms");
                return;
            }

            displayResults(probabilities, inputSymptoms);

        } catch (Exception e) {
            showError("Error: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private void displayResults(Map<String, Double> probabilities, Map<String, String> inputs) {
        // Get top 3 predictions
        List<Map.Entry<String, Double>> topPredictions = probabilities.entrySet().stream()
                .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                .limit(3)
                .collect(Collectors.toList());

        // Format results
        StringBuilder resultText = new StringBuilder("Top Predictions:\n");
        for (Map.Entry<String, Double> entry : topPredictions) {
            resultText.append(String.format("- %s (%.1f%%)\n", entry.getKey(), entry.getValue()));
        }

        result.setText(resultText.toString());
        result.setStyle("-fx-text-fill: black;");

        // Add to history
        String symptomInput = inputs.entrySet().stream()
                .map(e -> e.getKey() + ": " + e.getValue())
                .collect(Collectors.joining(", "));

        predictionHistory.add(new Prediction(
                LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss")),
                topPredictions.get(0).getKey(),
                topPredictions.get(0).getValue(),
                symptomInput));
    }

    private void showError(String message) {
        result.setText(message);
        result.setStyle("-fx-text-fill: red;");
    }
    @FXML
    private void goToFront(ActionEvent event) throws IOException {
        Parent root = FXMLLoader.load(getClass().getResource("/front.fxml"));
        Stage stage = (Stage)((Node)event.getSource()).getScene().getWindow();
        stage.setScene(new Scene(root));
        stage.show();
    }
}