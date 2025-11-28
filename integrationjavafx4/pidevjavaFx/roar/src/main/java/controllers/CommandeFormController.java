package controllers;

import com.stripe.Stripe;
import com.stripe.exception.StripeException;
import com.stripe.model.checkout.Session;
import com.stripe.param.checkout.SessionCreateParams;
import entite.Commande;
import entite.Medicament;
import entite.MedicamentCommande;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.print.PrinterJob;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.Stage;
import javafx.util.StringConverter;
import service.CommandeService;
import service.MedicamentService;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.time.LocalDate;
import java.util.Properties;
import java.util.ResourceBundle;

public class CommandeFormController implements Initializable {

    // FXML components unchanged
    @FXML private DatePicker dateCommandePicker;
    @FXML private ComboBox<Medicament> medicamentComboBox;
    @FXML private Spinner<Integer> quantiteSpinner;
    @FXML private ListView<String> medicamentListView;
    @FXML private Label totalPrixLabel;
    @FXML private Label dateError;
    @FXML private Label medicamentError;
    @FXML private Label quantiteError;

    @FXML
    private Button backButton;

    private final CommandeService commandeService = new CommandeService();
    private final MedicamentService medicamentService = new MedicamentService();
    private final Commande currentCommande = new Commande();


    private static final String SUCCESS_URL = "http://localhost:4242/success";
    private static final String CANCEL_URL = "http://localhost:4242/cancel";

    @Override
    public void initialize(URL url, ResourceBundle resourceBundle) {

        Properties props = loadConfig();
        String stripeApiKey = props.getProperty("stripe.api.key");

        if (stripeApiKey != null && !stripeApiKey.isEmpty()) {
            Stripe.apiKey = stripeApiKey;
        } else {
            System.err.println("Can't find stripe api key");
            showAlert(Alert.AlertType.ERROR, "Error in payments.");
        }

        medicamentComboBox.getItems().addAll(medicamentService.readAll());

        medicamentComboBox.setConverter(new StringConverter<Medicament>() {
            @Override
            public String toString(Medicament medicament) {
                return medicament != null ? medicament.getNom_medicament() : "";
            }

            @Override
            public Medicament fromString(String string) {
                return null;
            }
        });

        quantiteSpinner.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 100, 1));
        quantiteSpinner.valueProperty().addListener((obs, oldVal, newVal) -> updateTotalPrix());
        medicamentComboBox.valueProperty().addListener((obs, oldVal, newVal) -> updateTotalPrix());
    }


    private Properties loadConfig() {
        Properties props = new Properties();
        try (InputStream input = getClass().getClassLoader().getResourceAsStream("config.properties")) {
            if (input != null) {
                props.load(input);
            } else {
                System.err.println("Impossibile trovare il file config.properties");
            }
        } catch (IOException e) {
            System.err.println("Errore caricamento config: " + e.getMessage());
        }
        return props;
    }

    @FXML
    private void handleAddCommande() {
        clearErrors();
        boolean isValid = true;

        LocalDate dateCommande = dateCommandePicker.getValue();
        Medicament selectedMedicament = medicamentComboBox.getValue();
        int quantite = quantiteSpinner.getValue();

        if (dateCommande == null) {
            dateError.setText("Date requise.");
            isValid = false;
        } else if (dateCommande.isBefore(LocalDate.now())) {
            dateError.setText("La date ne peut pas être dans le passé.");
            isValid = false;
        }

        if (selectedMedicament == null) {
            medicamentError.setText("Médicament requis.");
            isValid = false;
        }

        if (quantite <= 0) {
            quantiteError.setText("Quantité invalide.");
            isValid = false;
        } else if (selectedMedicament != null && quantite > selectedMedicament.getQuantite_stock()) {
            quantiteError.setText("Quantité dépasse le stock disponible (" + selectedMedicament.getQuantite_stock() + ").");
            isValid = false;
        }

        if (!isValid) return;

        currentCommande.setDate_commande(dateCommande);
        currentCommande.addMedicament(selectedMedicament, quantite);
        medicamentListView.getItems().add(
                selectedMedicament.getNom_medicament() + " x" + quantite + " (" +
                        selectedMedicament.getPrix_medicament() * quantite + " DT)"
        );
        updateTotalPrix();
    }

    private void updateTotalPrix() {
        double total = currentCommande.getMedicaments().stream()
                .mapToDouble(mc -> mc.getMedicament().getPrix_medicament() * mc.getQuantite())
                .sum();

        currentCommande.setTotal_prix(total);
        totalPrixLabel.setText(String.format("%.2f DT", total));
    }

    @FXML
    private void handleSaveCommande() {
        handleAddCommande();

        if (currentCommande.getMedicaments().isEmpty()) {
            showAlert(Alert.AlertType.WARNING, "Veuillez ajouter au moins un médicament.");
            return;
        }

        try {
            Session session = createStripeSession();

            // Enregistrer la session Stripe
            currentCommande.setStripeSessionId(session.getId());
            currentCommande.setStatus("pending");
            commandeService.create(currentCommande);

            showStripePaymentPage(session.getUrl());
        } catch (StripeException e) {
            showAlert(Alert.AlertType.ERROR, "Erreur de paiement: " + e.getMessage());
        }
    }

    private Session createStripeSession() throws StripeException {
        SessionCreateParams.Builder paramsBuilder = SessionCreateParams.builder()
                .setMode(SessionCreateParams.Mode.PAYMENT)
                .setSuccessUrl(SUCCESS_URL)
                .setCancelUrl(CANCEL_URL);

        currentCommande.getMedicaments().forEach(mc -> {
            paramsBuilder.addLineItem(
                    SessionCreateParams.LineItem.builder()
                            .setPriceData(
                                    SessionCreateParams.LineItem.PriceData.builder()
                                            .setCurrency("eur")
                                            .setUnitAmount((long) (mc.getMedicament().getPrix_medicament() * 100))
                                            .setProductData(
                                                    SessionCreateParams.LineItem.PriceData.ProductData.builder()
                                                            .setName(mc.getMedicament().getNom_medicament())
                                                            .build()
                                            )
                                            .build()
                            )
                            .setQuantity((long) mc.getQuantite())
                            .build()
            );
        });

        return Session.create(paramsBuilder.build());
    }

    private void showStripePaymentPage(String checkoutUrl) {
        Stage stage = new Stage();
        WebView webView = new WebView();
        WebEngine webEngine = webView.getEngine();

        webEngine.locationProperty().addListener((obs, oldVal, newVal) -> {
            if (newVal != null) handlePaymentResult(newVal, stage);
        });

        webEngine.load(checkoutUrl);
        stage.setScene(new Scene(webView));
        stage.show();
    }

    private void handlePaymentResult(String url, Stage paymentStage) {
        if (url.startsWith(SUCCESS_URL)) {
            Platform.runLater(() -> {
                paymentStage.close();

                // Mettre à jour le statut
                currentCommande.setStatus("paid");
                commandeService.update(currentCommande);

                saveCommandeAndRedirect();
                generatePdf(currentCommande);
            });
        } else if (url.startsWith(CANCEL_URL)) {
            Platform.runLater(() -> {
                paymentStage.close();
                showAlert(Alert.AlertType.INFORMATION, "Paiement annulé");
            });
        }
    }

    private void saveCommandeAndRedirect() {
        try {
            commandeService.create(currentCommande);

            currentCommande.getMedicaments().forEach(mc -> {
                Medicament medicament = mc.getMedicament();
                medicament.setQuantite_stock(medicament.getQuantite_stock() - mc.getQuantite());
                medicamentService.update(medicament);
            });

            FXMLLoader loader = new FXMLLoader(getClass().getResource("/commande_list.fxml"));
            Parent root = loader.load();
            Stage currentStage = (Stage) totalPrixLabel.getScene().getWindow();
            currentStage.setScene(new Scene(root));
        } catch (IOException e) {
            showAlert(Alert.AlertType.ERROR, "Erreur de redirection: " + e.getMessage());
        }
    }

    private void generatePdf(Commande commande) {
        try {
            StringBuilder html = new StringBuilder();
            html.append("<html><head><style>")
                    .append("body { font-family: Arial, sans-serif; margin: 20px; }")
                    .append(".header { display: flex; align-items: center; margin-bottom: 20px; }")
                    .append(".logo { height: 80px; margin-right: 20px; }")
                    .append(".title { flex-grow: 1; }")
                    .append("h1 { margin: 0; color: #2c3e50; }")
                    .append(".date { color: #7f8c8d; font-size: 14px; }")
                    .append("table { width: 100%; border-collapse: collapse; margin-top: 20px; }")
                    .append("th { background-color: #3498db; color: white; text-align: left; padding: 10px; }")
                    .append("td { padding: 8px; border-bottom: 1px solid #ddd; }")
                    .append("tr:nth-child(even) { background-color: #f2f2f2; }")
                    .append(".footer { margin-top: 20px; text-align: right; font-size: 12px; color: #7f8c8d; }")
                    .append("</style></head><body>")

                    .append("<div class='header'>")
                    .append("<img class='logo' src='").append(getClass().getResource("/img/logo.png")).append("'/>")
                    .append("<div class='title'>")
                    .append("<h1>Facture Commande #").append(commande.getId()).append("</h1>")
                    .append("<div class='date'>Date: ").append(commande.getDate_commande()).append("</div>")
                    .append("</div></div>")

                    .append("<table><thead><tr>")
                    .append("<th>Médicament</th><th>Quantité</th><th>Prix Unitaire</th><th>Total</th>")
                    .append("</tr></thead><tbody>");

            for (MedicamentCommande mc : commande.getMedicaments()) {
                double total = mc.getQuantite() * mc.getMedicament().getPrix_medicament();
                html.append("<tr>")
                        .append("<td>").append(mc.getMedicament().getNom_medicament()).append("</td>")
                        .append("<td>").append(mc.getQuantite()).append("</td>")
                        .append("<td>").append(String.format("%.2f DT", mc.getMedicament().getPrix_medicament())).append("</td>")
                        .append("<td>").append(String.format("%.2f DT", total)).append("</td>")
                        .append("</tr>");
            }

            html.append("</tbody></table>")
                    .append("<div class='footer'>")
                    .append("Total: ").append(String.format("%.2f DT", commande.getTotal_prix()))
                    .append("</div></body></html>");

            // Use WebView to render the HTML
            WebView webView = new WebView();
            WebEngine webEngine = webView.getEngine();
            webEngine.loadContent(html.toString());

            // Print dialog and print
            PrinterJob job = PrinterJob.createPrinterJob();
            if (job != null) {
                job.showPrintDialog(null);
                webEngine.print(job);
                job.endJob();
                showAlert(Alert.AlertType.INFORMATION, "Facture exportée avec succès !");
            }

        } catch (Exception e) {
            e.printStackTrace();
            showAlert(Alert.AlertType.ERROR, "Erreur lors de l'export PDF : " + e.getMessage());
        }
    }


    private void resetForm() {
        dateCommandePicker.setValue(null);
        medicamentComboBox.getSelectionModel().clearSelection();
        quantiteSpinner.getValueFactory().setValue(1);
        medicamentListView.getItems().clear();
        totalPrixLabel.setText("0.00 DT");
        currentCommande.getMedicaments().clear();
        currentCommande.setTotal_prix(0);
    }

    private void showAlert(Alert.AlertType type, String message) {
        new Alert(type, message, ButtonType.OK).show();
    }

    private void clearErrors() {
        dateError.setText("");
        medicamentError.setText("");
        quantiteError.setText("");
    }

    @FXML
    private void handleBackButtoncataloguecommande() {
        try {
            Stage stage = (Stage) backButton.getScene().getWindow();
            Parent root = FXMLLoader.load(getClass().getResource("/catalogue.fxml"));
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.show();
        } catch (Exception e) {
            e.printStackTrace();
            showAlert("Error", "Could not return to catalogue");
        }
    }

    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}