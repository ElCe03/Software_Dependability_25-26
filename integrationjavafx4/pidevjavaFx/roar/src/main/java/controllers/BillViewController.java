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

    /*@ public invariant pdfPreview != null ==> pdfPreview.getEngine() != null;
      @ public invariant currentCommande != null ==> pdfBytes != null || pdfBytes == null;
      @*/

    /*@
      @ requires commande != null;
      @ requires commande.getId() != null;
      @ requires pdfPreview != null;
      @ ensures this.currentCommande == commande;
      @ ensures this.pdfBytes != null;
      @ ensures this.pdfBytes.length > 0;
      @ assignable this.currentCommande, this.pdfBytes, pdfPreview.*;
      @*/
    public void initialize(Commande commande) {
        //@ assert commande != null;
        //@ assert pdfPreview != null;

        this.currentCommande = commande;

        //@ assert this.currentCommande != null;
        //@ assert this.currentCommande == commande;

        showPreview();

        //@ assert this.pdfBytes != null;
        //@ assert this.pdfBytes.length > 0;
    }

    /*@
      @ requires currentCommande != null;
      @ requires pdfPreview != null;
      @ requires pdfPreview.getEngine() != null;
      @ ensures pdfBytes != null;
      @ ensures pdfBytes.length > 0;
      @ assignable pdfBytes, pdfPreview.*;
      @*/
    private void showPreview() {
        //@ assert currentCommande != null;
        //@ assert pdfPreview != null;

        // Générer le PDF en mémoire
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        //@ assert output != null;

        generatePdf(output);

        pdfBytes = output.toByteArray();

        //@ assert pdfBytes != null;
        //@ assert pdfBytes.length > 0;

        // Afficher l'aperçu
        WebEngine engine = pdfPreview.getEngine();
        //@ assert engine != null;

        engine.loadContent(new String(pdfBytes, StandardCharsets.UTF_8));
    }

    /*@
      @ requires downloadButton != null;
      @ requires downloadButton.getScene() != null;
      @ requires downloadButton.getScene().getWindow() != null;
      @ requires currentCommande != null;
      @ requires currentCommande.getId() != null;
      @ requires pdfBytes != null;
      @ requires pdfBytes.length > 0;
      @*/
    @FXML
    private void handleDownload() {
        //@ assert downloadButton != null;
        //@ assert currentCommande != null;
        //@ assert currentCommande.getId() != null;
        //@ assert pdfBytes != null;
        //@ assert pdfBytes.length > 0;

        FileChooser fileChooser = new FileChooser();
        //@ assert fileChooser != null;

        fileChooser.setTitle("Enregistrer la facture");

        String fileName = "facture_" + currentCommande.getId() + ".pdf";
        //@ assert fileName != null;
        //@ assert fileName.endsWith(".pdf");

        fileChooser.setInitialFileName(fileName);

        fileChooser.getExtensionFilters().add(
                new FileChooser.ExtensionFilter("PDF Files", "*.pdf"));

        File file = fileChooser.showSaveDialog(downloadButton.getScene().getWindow());

        if (file != null) {
            //@ assert file != null;
            //@ assert pdfBytes != null;

            try (FileOutputStream fos = new FileOutputStream(file)) {
                //@ assert fos != null;

                fos.write(pdfBytes);

                //@ assert file.exists();
                //@ assert file.length() == pdfBytes.length;

                showAlert("Téléchargement réussi!", Alert.AlertType.INFORMATION);
            } catch (IOException e) {
                //@ assert e != null;
                showAlert("Erreur d'écriture: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
        // else: user cancelled, no action needed
    }

    /*@
      @ requires output != null;
      @ requires currentCommande != null;
      @ signals_only RuntimeException;
      @ signals (RuntimeException e) e.getCause() instanceof IOException;
      @*/
    private void generatePdf(OutputStream output) {
        //@ assert output != null;
        //@ assert currentCommande != null;

        try (PDDocument doc = new PDDocument()) {
            //@ assert doc != null;

            PDPage page = new PDPage();
            //@ assert page != null;

            doc.addPage(page);

            //@ assert doc.getNumberOfPages() > 0;

            // ... (votre code de génération PDF existant)

            doc.save(output);

        } catch (IOException e) {
            //@ assert e != null;
            throw new RuntimeException("Erreur de génération PDF", e);
        }
    }

    /*@
      @ requires message != null;
      @ requires type != null;
      @ requires !message.isEmpty();
      @*/
    private void showAlert(String message, Alert.AlertType type) {
        //@ assert message != null && !message.isEmpty();
        //@ assert type != null;

        Alert alert = new Alert(type);
        //@ assert alert != null;

        alert.setContentText(message);

        //@ assert alert.getContentText().equals(message);

        alert.showAndWait();
    }
}