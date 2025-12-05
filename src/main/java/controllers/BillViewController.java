package controllers;

import entite.Commande;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.pdmodel.PDPage;


import java.io.*;
import java.nio.charset.StandardCharsets;


public class BillViewController {
    @FXML private WebView pdfPreview;
    @FXML private Button downloadButton;

    private Commande currentCommande;
    private byte[] pdfBytes;

    public void initialize(Commande commande) {
        this.currentCommande = commande;
        showPreview();
    }

    private void showPreview() {
        // Générer le PDF en mémoire
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        generatePdf(output);
        pdfBytes = output.toByteArray();

        // Afficher l'aperçu
        WebEngine engine = pdfPreview.getEngine();
        engine.loadContent(new String(pdfBytes, StandardCharsets.UTF_8));
    }

    @FXML
    private void handleDownload() {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Enregistrer la facture");
        fileChooser.setInitialFileName("facture_" + currentCommande.getId() + ".pdf");
        fileChooser.getExtensionFilters().add(
                new FileChooser.ExtensionFilter("PDF Files", "*.pdf"));

        File file = fileChooser.showSaveDialog(downloadButton.getScene().getWindow());

        if (file != null) {
            try (FileOutputStream fos = new FileOutputStream(file)) {
                fos.write(pdfBytes);
                showAlert("Téléchargement réussi!", Alert.AlertType.INFORMATION);
            } catch (IOException e) {
                showAlert("Erreur d'écriture: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
    }

    private void generatePdf(OutputStream output) {
        try (PDDocument doc = new PDDocument()) {
            PDPage page = new PDPage();
            doc.addPage(page);

            // ... (votre code de génération PDF existant)

            doc.save(output);
        } catch (IOException e) {
            throw new RuntimeException("Erreur de génération PDF", e);
        }
    }

    private void showAlert(String message, Alert.AlertType type) {
        Alert alert = new Alert(type);
        alert.setContentText(message);
        alert.showAndWait();
    }

}
