package controllers;

import com.itextpdf.text.*;
import com.itextpdf.text.Font;
import com.itextpdf.text.pdf.PdfPCell;
import com.itextpdf.text.pdf.PdfWriter;
import com.itextpdf.text.pdf.PdfPTable;
import javafx.application.Platform;
import javafx.concurrent.Worker;
import javafx.print.PrinterJob;
import javafx.scene.Group;
import javafx.scene.web.WebView;
import javafx.scene.web.WebEngine;
import javafx.scene.control.Alert;
import javafx.print.PrinterJob;
import javafx.scene.web.WebView;
import javafx.scene.web.WebEngine;
import java.time.LocalDate;


import entite.Entretien;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.Button;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.layout.HBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.Modality;
import javafx.stage.Stage;
import service.EntretienService;

import java.awt.*;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.LocalDate;

public class ListeEntretienController {

    @FXML
    private TableView<Entretien> entretienTable;

    @FXML
    private TableColumn<Entretien, String> nomColumn;

    @FXML
    private TableColumn<Entretien, LocalDate> dateColumn;

    @FXML
    private TableColumn<Entretien, String> descriptionColumn;

    @FXML
    private TableColumn<Entretien, Void> actionsColumn;

    @FXML
    private TableColumn<Entretien, Void> pdfColumn;

    private final EntretienService entretienService = new EntretienService();

    @FXML
    public void initialize() {
        nomColumn.setCellValueFactory(new PropertyValueFactory<>("nomEquipement"));
        dateColumn.setCellValueFactory(new PropertyValueFactory<>("date"));
        descriptionColumn.setCellValueFactory(new PropertyValueFactory<>("description"));

        addActionButtonsToTable();
        addPdfButtonToTable();

        loadEntretienData();
    }

    private void loadEntretienData() {
        entretienTable.getItems().setAll(entretienService.getAllEntretiens());
    }

    private void addActionButtonsToTable() {
        actionsColumn.setCellFactory(column -> new TableCell<>() {
            private final Button btnModifier = new Button("Modifier");
            private final Button btnSupprimer = new Button("Supprimer");
            private final HBox hbox = new HBox(10, btnModifier, btnSupprimer);

            {
                btnModifier.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white;");
                btnSupprimer.setStyle("-fx-background-color: #F44336; -fx-text-fill: white;");

                btnModifier.setOnAction(event -> {
                    Entretien entretien = getTableView().getItems().get(getIndex());
                    handleModifier(entretien);
                });

                btnSupprimer.setOnAction(event -> {
                    Entretien entretien = getTableView().getItems().get(getIndex());
                    handleSupprimer(entretien);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                if (empty) {
                    setGraphic(null);
                } else {
                    setGraphic(hbox);
                }
            }
        });
    }

    private void addPdfButtonToTable() {
        pdfColumn.setCellFactory(column -> new TableCell<>() {
            private final Button btnGenererPdf = new Button("Générer PDF");
            private final HBox hbox = new HBox(10, btnGenererPdf);

            {
                btnGenererPdf.setStyle("-fx-background-color: #2196F3; -fx-text-fill: white;");
                btnGenererPdf.setOnAction(event -> {
                    Entretien entretien = getTableView().getItems().get(getIndex());
                    handleGenererPdf(entretien);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                if (empty) {
                    setGraphic(null);
                } else {
                    setGraphic(hbox);
                }
            }
        });
    }

    private void handleModifier(Entretien entretien) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/ModifierEntretien.fxml"));
            Parent root = loader.load();

            ModifierEntretienController controller = loader.getController();
            controller.initData(entretien);
            controller.setOnEntretienModifie(() -> loadEntretienData());

            Stage stage = new Stage();
            stage.setTitle("Modifier Entretien");
            stage.setScene(new Scene(root));
            stage.show();
        } catch (IOException e) {
            System.err.println("❌ Erreur lors du chargement de la page de modification : " + e.getMessage());
        }
    }

    private void handleSupprimer(Entretien entretien) {
        entretienService.deleteEntretien(entretien.getId());
        entretienTable.getItems().remove(entretien);
        System.out.println("🗑 Entretien supprimé : " + entretien.getNomEquipement());
    }

    @FXML
    private void handleGenererPdf(Entretien entretien) {
        if (entretien == null) {
            showAlert("Erreur", "L'objet Entretien est null");
            return;
        }

        try {
            // 1. Create HTML content
            String html = buildHtmlContent(entretien);

            // 2. Create WebView and load content
            WebView webView = new WebView();
            webView.getEngine().loadContent(html);

            // 3. Create and show a temporary stage
            Stage tempStage = new Stage();
            tempStage.initModality(Modality.APPLICATION_MODAL);
            tempStage.setScene(new Scene(new Group(webView)));

            // 4. Properly wait for WebView to render
            webView.getEngine().getLoadWorker().stateProperty().addListener((obs, oldState, newState) -> {
                if (newState == Worker.State.SUCCEEDED) {
                    // 5. Now show the print dialog
                    PrinterJob job = PrinterJob.createPrinterJob();
                    if (job != null && job.showPrintDialog(tempStage)) {
                        boolean success = job.printPage(webView);
                        if (success) {
                            job.endJob();
                            showAlert("Succès", "PDF généré avec succès");
                        } else {
                            showAlert("Erreur", "Échec de la génération du PDF");
                        }
                    }
                    tempStage.close();
                }
            });

            tempStage.show(); // Important: must show the stage

        } catch (Exception e) {
            showAlert("Erreur", "Erreur lors de la génération du PDF: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private String buildHtmlContent(Entretien entretien) {
        return "<html><head><style>"
                + "body { font-family: Arial, sans-serif; margin: 20px; }"
                + ".header { display: flex; align-items: center; margin-bottom: 20px; }"
                + ".logo { height: 80px; margin-right: 20px; }"
                + ".title { flex-grow: 1; }"
                + "h1 { margin: 0; color: #2c3e50; }"
                + ".date { color: #7f8c8d; font-size: 14px; }"
                + ".info-section { margin-top: 30px; }"
                + ".info-label { font-weight: bold; color: #3498db; width: 150px; display: inline-block; }"
                + ".info-value { margin-left: 10px; }"
                + ".description-box { border: 1px solid #ddd; padding: 15px; margin-top: 20px; border-radius: 5px; }"
                + ".footer { margin-top: 40px; text-align: right; font-size: 12px; color: #7f8c8d; }"
                + "</style></head><body>"
                + "<div class='header'>"
                + "<img class='logo' src='" + getClass().getResource("/img/logo.png") + "'/>"
                + "<div class='title'>"
                + "<h1>Fiche d'Entretien</h1>"
                + "<div class='date'>Généré le: " + LocalDate.now() + "</div>"
                + "</div></div>"
                + "<div class='info-section'>"
                + "<div><span class='info-label'>ID Entretien:</span><span class='info-value'>" + entretien.getId() + "</span></div>"
                + "<div><span class='info-label'>Équipement:</span><span class='info-value'>" + entretien.getNomEquipement() + "</span></div>"
                + "<div><span class='info-label'>Date prévue:</span><span class='info-value'>" + entretien.getDate() + "</span></div>"
                + "<div><span class='info-label'>Statut:</span><span class='info-value'>En maintenance</span></div>"
                + "</div>"
                + "<div class='description-box'>"
                + "<div class='info-label'>Description:</div>"
                + "<p>" + entretien.getDescription() + "</p>"
                + "</div>"
                + "<div class='footer'>"
                + "Document généré automatiquement par le système de gestion"
                + "</div></body></html>";
    }
    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}

