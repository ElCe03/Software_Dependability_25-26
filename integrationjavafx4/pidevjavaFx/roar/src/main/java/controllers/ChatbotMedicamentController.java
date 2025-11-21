package controllers;

import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.ListView;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import service.MedicamentService;
import test.MainFx;

import java.io.IOException;
import java.text.Normalizer;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ChatbotMedicamentController {

    /*@
      @ private invariant apiService != null;
      @ private invariant medicamentService != null;
      @ private invariant searchHistory != null;
      @ private invariant LOCAL_MEDICAMENT_INFO != null;
      @*/

    /*@
      @ private invariant waitingForSelection ==>
      @    (lastSearchResults != null && lastSearchResults.length() > 0);
      @*/
    private final MedicamentAPIService apiService = new MedicamentAPIService();
    private final MedicamentService medicamentService = new MedicamentService();
    private JSONArray lastSearchResults;
    private boolean waitingForSelection = false;

    @FXML private ScrollPane chatScrollPane;
    @FXML private VBox chatMessagesContainer;
    @FXML private TextField userInputField;
    @FXML private Button sendButton;
    @FXML private ListView<String> suggestionsListView;

    private ObservableList<String> searchHistory = FXCollections.observableArrayList();
    private static final Map<String, String> LOCAL_MEDICAMENT_INFO = new LinkedHashMap<String, String>() {{
        put("ibuprofen", createLocalInfo("Ibuprofen", "Douleurs, inflammation", "200-400 mg/4-6h"));
        put("acetaminophen", createLocalInfo("Acetaminophen", "Douleurs, fièvre", "500-1000 mg/4-6h"));
    }};

    /*@ public normal_behavior
      @   requires chatScrollPane != null;
      @   requires chatMessagesContainer != null;
      @   requires userInputField != null;
      @   requires sendButton != null;
      @   requires suggestionsListView != null;
      @
      @   assignable chatScrollPane.vvalueProperty(),
      @              sendButton.onActionProperty(),
      @              userInputField.onActionProperty(),
      @              suggestionsListView.itemsProperty(),
      @              suggestionsListView.selectionModel.selectedItemProperty(),
      @              userInputField.textProperty(),
      @              chatMessagesContainer.children;
      @
      @   ensures suggestionsListView.getItems().size() == LOCAL_MEDICAMENT_INFO.size();
      @   ensures !chatMessagesContainer.getChildren().isEmpty();
      @*/
    @FXML
    private void initialize() {
        configureUIComponents();
        initializeChat();
    }

    private void configureUIComponents() {
        chatScrollPane.vvalueProperty().bind(chatMessagesContainer.heightProperty());
        sendButton.setOnAction(e -> handleUserMessage());
        userInputField.setOnAction(e -> handleUserMessage());

        suggestionsListView.setItems(FXCollections.observableArrayList(LOCAL_MEDICAMENT_INFO.keySet()));
        suggestionsListView.getSelectionModel().selectedItemProperty().addListener(
                (obs, oldVal, newVal) -> handleSuggestionSelection(newVal));

        userInputField.textProperty().addListener((obs, oldVal, newVal) ->
                updateSuggestions(newVal.trim().toLowerCase()));
    }

    private void initializeChat() {
        Platform.runLater(() -> {
            addBotMessage("Bonjour ! Je suis votre assistant médicament intelligent. 😊");
            addBotMessage("Exemples de requêtes :\n• Effets de l'ibuprofène\n• Dosage du paracétamol\n• Contre-indications de l'oméprazole");
        });
    }

    private void handleSuggestionSelection(String selectedMed) {
        if (selectedMed != null) {
            userInputField.setText(selectedMed);
            handleUserMessage();
        }
    }

    private void updateSuggestions(String input) {
        List<String> filtered = LOCAL_MEDICAMENT_INFO.keySet().stream()
                .filter(k -> k.toLowerCase().contains(input.toLowerCase()))
                .limit(10)
                .toList();
        suggestionsListView.setItems(FXCollections.observableArrayList(filtered));
    }
    /*@ public normal_behavior
          @   requires userInputField != null;
          @   requires chatMessagesContainer != null;
          @
          @   assignable userInputField.textProperty(),
          @              chatMessagesContainer.children,
          @              searchHistory,
          @              waitingForSelection,
          @              lastSearchResults;
          @
          @   ensures !\old(userInputField.getText().trim().isEmpty()) ==>
          @           userInputField.getText().isEmpty();
          @*/
    private void handleUserMessage() {
        String message = userInputField.getText().trim();
        if (message.isEmpty()) return;

        addUserMessage(message);
        userInputField.clear();
        processMessage(message);
    }
    /*@ private behavior
          @   requires message != null;
          @
          @   when \old(waitingForSelection) == true;
          @   assignable waitingForSelection, chatMessagesContainer.children;
          @   ensures waitingForSelection == false;
          @
          @   also
          @   when \old(waitingForSelection) == false;
          @   assignable searchHistory, chatMessagesContainer.children;
          @   ensures searchHistory.contains(message) || \old(searchHistory.size()) == 10;
          @*/
    private void processMessage(String message) {
        if (waitingForSelection) {
            handleMultipleChoiceSelection(message);
            return;
        }

        updateSearchHistory(message);
        String medicamentName = extractMedicamentName(message);
        searchMedicament(medicamentName != null ? medicamentName : message);
    }

    private void updateSearchHistory(String query) {
        if (!searchHistory.contains(query)) {
            searchHistory.add(0, query);
            if (searchHistory.size() > 10) {
                searchHistory.remove(10);
            }
        }
    }

    private String extractMedicamentName(String message) {
        Pattern pattern = Pattern.compile(
                "(?i)(effets|dosage|contre-indications|utilisation|interactions)\\s+(de|du|des|d'|pour)\\s+([^\\d\\s]+)");
        Matcher matcher = pattern.matcher(message);
        return matcher.find() ? normalizeTerm(matcher.group(3)) : null;
    }
    /*@ private normal_behavior
          @   requires medicamentName != null;
          @   assignable chatMessagesContainer.children;
          @*/
    private void searchMedicament(String medicamentName) {
        addBotMessage("🔍 Recherche de '" + medicamentName + "'...");

        new Thread(() -> {
            try {
                String normalized = normalizeTerm(medicamentName);
                if (LOCAL_MEDICAMENT_INFO.containsKey(normalized)) {
                    Platform.runLater(() -> addBotMessage(LOCAL_MEDICAMENT_INFO.get(normalized)));
                    return;
                }

                String apiResponse = apiService.chercherMedicamentComplet(medicamentName);
                processAPIResponse(apiResponse, medicamentName);
            } catch (Exception e) {
                Platform.runLater(() ->
                        addBotMessage("⚠️ Erreur de connexion. Vérifiez votre accès Internet."));
            }
        }).start();
    }
    /*@ private normal_behavior
          @   requires response != null && medicamentName != null;
          @   assignable lastSearchResults, waitingForSelection, chatMessagesContainer.children;
          @*/
    private void processAPIResponse(String response, String medicamentName) {
        try {
            JSONObject json = new JSONObject(response);

            // Vérifier les erreurs de l'API FDA
            if (json.has("error")) {
                throw new IOException("Erreur FDA : " + json.getString("error"));
            }

            // Vérifier la présence de résultats
            if (!json.has("results") || json.getJSONArray("results").length() == 0) {
                throw new JSONException("Aucun résultat trouvé");
            }

            JSONArray results = json.getJSONArray("results");
            lastSearchResults = results;

            Platform.runLater(() -> {
                if (results.length() > 1) {
                    showMultipleResults(medicamentName);
                } else {
                    displayMedicationInfo(results.getJSONObject(0));
                }
            });

        } catch (JSONException e) {
            // Fallback local si échec du parsing JSON
            Platform.runLater(() -> {
                String normalizedName = normalizeTerm(medicamentName);
                if (LOCAL_MEDICAMENT_INFO.containsKey(normalizedName)) {
                    addBotMessage(LOCAL_MEDICAMENT_INFO.get(normalizedName));
                } else {
                    addBotMessage("⚠️ Aucune information disponible pour : " + medicamentName);
                }
            });
        } catch (IOException e) {
            // Gestion des erreurs réseau
            Platform.runLater(() -> {
                addBotMessage("🔴 Erreur serveur : " + e.getMessage());
                addBotMessage("Vérifiez l'orthographe ou essayez ultérieurement");
            });
        } catch (Exception e) {
            // Catch-all pour autres exceptions
            Platform.runLater(() -> {
                addBotMessage("⚠️ Erreur inattendue : " + e.getClass().getSimpleName());
            });
        }
    }

    private void handleNoResults(String medicamentName) {
        addBotMessage("Aucune information trouvée pour : " + medicamentName);
    }
    /*@ private normal_behavior
          @   requires medicamentName != null;
          @   requires lastSearchResults != null && lastSearchResults.length() > 1;
          @   assignable waitingForSelection, chatMessagesContainer.children;
          @   ensures waitingForSelection == true;
          @*/
    private void showMultipleResults(String medicamentName) {
        StringBuilder sb = new StringBuilder("Plusieurs résultats trouvés :\n");
        for (int i = 0; i < lastSearchResults.length(); i++) {
            JSONObject med = lastSearchResults.getJSONObject(i);
            sb.append(i + 1).append(". ")
                    .append(extractBrandName(med))
                    .append("\n");
        }
        sb.append("\nRépondez par le numéro correspondant (1-").append(lastSearchResults.length()).append(")");
        addBotMessage(sb.toString());
        waitingForSelection = true;
    }

    private String extractBrandName(JSONObject medData) {
        try {
            return medData.getJSONObject("openfda")
                    .getJSONArray("brand_name")
                    .getString(0);
        } catch (JSONException e) {
            return "Nom commercial inconnu";
        }
    }
    /*@ private normal_behavior
          @   requires input != null;
          @   requires lastSearchResults != null;
          @   assignable waitingForSelection, chatMessagesContainer.children;
          @   ensures waitingForSelection == false;
          @*/
    private void handleMultipleChoiceSelection(String input) {
        try {
            int choice = Integer.parseInt(input.trim()) - 1;
            if (choice >= 0 && choice < lastSearchResults.length()) {
                displayMedicationInfo(lastSearchResults.getJSONObject(choice));
            }
        } catch (NumberFormatException e) {
            addBotMessage("Veuillez entrer un numéro valide.");
        }
        waitingForSelection = false;
    }

    private void displayMedicationInfo(JSONObject medData) {
        StringBuilder info = new StringBuilder();
        info.append(extractField(medData, "openfda.brand_name", "Nom commercial"));
        info.append(extractField(medData, "description", "Description"));
        info.append(extractField(medData, "indications_and_usage", "Indications"));
        info.append(extractField(medData, "dosage_and_administration", "Posologie"));
        info.append(extractField(medData, "warnings", "Mises en garde"));

        addBotMessage(info.toString());
    }

    private String extractField(JSONObject medData, String fieldPath, String displayName) {
        try {
            String[] parts = fieldPath.split("\\.");
            JSONObject current = medData;
            for (int i = 0; i < parts.length - 1; i++) {
                current = current.getJSONObject(parts[i]);
            }
            String value = current.getJSONArray(parts[parts.length-1]).getString(0);
            return String.format("• %s : \n%s\n\n", displayName, value);
        } catch (JSONException e) {
            return "";
        }
    }

    private static String createLocalInfo(String nom, String usage, String dosage) {
        return String.format(
                "🏷 %s\n\n⚕️ Usage : %s\n💊 Posologie : %s\n\n(Info locale)",
                nom, usage, dosage);
    }

    private String normalizeTerm(String term) {
        return Normalizer.normalize(term, Normalizer.Form.NFD)
                .replaceAll("[^\\p{ASCII}]", "")
                .toLowerCase()
                .replaceAll("[^a-z]", "");
    }

    private void addUserMessage(String message) {
        addMessage(message, true, "#DCF8C6");
    }

    private void addBotMessage(String message) {
        addMessage(message, false, "#FFFFFF");
    }

    private void addMessage(String text, boolean isUser, String color) {
        HBox container = new HBox();
        container.setPadding(new Insets(5));
        container.setAlignment(isUser ? Pos.CENTER_RIGHT : Pos.CENTER_LEFT);

        TextFlow messageFlow = new TextFlow(new Text(text));
        messageFlow.setPadding(new Insets(10));
        messageFlow.setMaxWidth(chatScrollPane.getWidth() * 0.75);
        messageFlow.setStyle("-fx-background-color: " + color + ";"
                + "-fx-background-radius: 15;"
                + "-fx-padding: 10;");

        container.getChildren().add(messageFlow);
        Platform.runLater(() -> chatMessagesContainer.getChildren().add(container));
    }

    @FXML
    private void handleBackButton() {
        MainFx.loadPage("medicament.fxml");
    }
}