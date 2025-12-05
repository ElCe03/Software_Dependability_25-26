package controllers;

import entite.Commande;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import service.CommandeService;
import test.MainFx;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

public class CommandeListController {

    private final CommandeService commandeService = new CommandeService();
    private final ObservableList<Commande> commandeData = FXCollections.observableArrayList();

    @FXML private TableView<Commande> commandeTable;
    @FXML private TableColumn<Commande, Integer> idColumn;
    @FXML private TableColumn<Commande, LocalDate> dateCommandeColumn;

    @FXML private TableColumn<Commande, Double> totalPrixColumn;
    @FXML private TableColumn<Commande, Integer> quantiteColumn;
    @FXML private TableColumn<Commande, String> medicamentsColumn;
    @FXML private TableColumn<Commande, Void> modifyColumn;
    @FXML private TableColumn<Commande, Void> deleteColumn;
  //  @FXML private TableColumn<Commande, Void> downloadColumn;
    @FXML private TextField searchField;
    @FXML private ComboBox<String> sortComboBox;
    @FXML private Pagination pagination;

    private static final int ITEMS_PER_PAGE = 10;
    private FilteredList<Commande> filteredData;
    @FXML
    private void initialize() {
        commandeTable.setStyle("-fx-background-insets: 0; -fx-padding: 0;");

        configureTableColumns();
        addTableButtons();
        refreshTableData();
       // addDownloadButtonToTable();
        setupSorting();
        setupSearch();
        setupPagination();

    }

    private void configureTableColumns() {
        idColumn.setCellValueFactory(new PropertyValueFactory<>("id"));
        dateCommandeColumn.setCellValueFactory(new PropertyValueFactory<>("date_commande"));
        totalPrixColumn.setCellValueFactory(new PropertyValueFactory<>("total_prix"));
        quantiteColumn.setCellValueFactory(new PropertyValueFactory<>("quantite"));
        medicamentsColumn.setCellValueFactory(cellData ->
                new ReadOnlyStringWrapper(cellData.getValue().getNomMedicamentsCommandes())
        );
    }

    private void addTableButtons() {
        addModifyButtonToTable();
        addDeleteButtonToTable();
    }

    private void addModifyButtonToTable() {
        modifyColumn.setCellFactory(param -> new TableCell<>() {
            private final Button modifyBtn = new Button("Modifier");

            {
                modifyBtn.setStyle("-fx-background-color: #007bff; -fx-text-fill: white; -fx-cursor: hand;");
                modifyBtn.setOnAction(e -> {
                    Commande c = getTableView().getItems().get(getIndex());
                    handleModify(c);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : modifyBtn);
            }
        });
    }

    private void addDeleteButtonToTable() {
        deleteColumn.setCellFactory(param -> new TableCell<>() {
            private final Button deleteBtn = new Button("Supprimer");

            {
                deleteBtn.setStyle("-fx-background-color: #dc3545; -fx-text-fill: white; -fx-cursor: hand;");
                deleteBtn.setOnAction(e -> {
                    Commande c = getTableView().getItems().get(getIndex());
                    handleDeleteConfirmation(c);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : deleteBtn);
            }
        });
    }
  /*  private void addDownloadButtonToTable() {
        downloadColumn.setCellFactory(param -> new TableCell<>() {
            private final Button downloadBtn = new Button("PDF");

            {
                downloadBtn.setOnAction(e -> {
                    Commande commande = getTableView().getItems().get(getIndex());
                    handleDownloadPdf(commande);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : downloadBtn);
            }
        });
    }*/
    @FXML
    private void handleNewCommande() {
        MainFx.loadPage("commande.fxml"); // Assure-toi que ce fichier existe dans tes ressources
    }

    private void showAlert(String message, Alert.AlertType type) {
        Alert alert = new Alert(type);
        alert.setContentText(message);
        alert.showAndWait();
    }
    private void handleModify(Commande c) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/commande_update.fxml"));
            Parent root = loader.load();

            CommandeUpdateController controller = loader.getController();
            controller.setCommande(c);

            Stage stage = (Stage) commandeTable.getScene().getWindow();
            stage.setScene(new Scene(root));
            stage.show();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void handleDeleteConfirmation(Commande c) {
        Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
        alert.setTitle("Confirmation de suppression");
        alert.setHeaderText("Supprimer la commande #" + c.getId() + " ?");
        alert.setContentText("Cette action est irréversible.");

        Optional<ButtonType> result = alert.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            commandeService.delete(c);
            refreshTableData();
        }
    }

    private void refreshTableData() {
        commandeData.setAll(commandeService.readAll());
        filteredData = new FilteredList<>(commandeData);
        pagination.setPageCount(calculatePageCount());
    }

    @FXML
    private void handleDownloadPdf(Commande selected) {
        if (selected != null && "paid".equals(selected.getStatus())) {
            generateAndDownloadPdf(selected);
        } else {
            showAlert("Seules les commandes payées peuvent être téléchargées", Alert.AlertType.WARNING);
        }
    }

    private void generateAndDownloadPdf(Commande commande) {
        try {
            // Créer le dossier si inexistant
            Path outputDir = Paths.get("factures");
            if (!Files.exists(outputDir)) {
                Files.createDirectories(outputDir);
            }

            Path pdfPath = outputDir.resolve("commande_" + commande.getId() + ".pdf");

            // Générer le PDF (à implémenter)
            // generatePdfContent(commande, pdfPath);

            FileChooser fileChooser = new FileChooser();
            fileChooser.setTitle("Enregistrer la facture");
            fileChooser.setInitialFileName(pdfPath.getFileName().toString());

            // Positionner la fenêtre de dialogue correctement
            Stage stage = (Stage) commandeTable.getScene().getWindow();
            File file = fileChooser.showSaveDialog(stage);

            if (file != null) {
                Files.copy(pdfPath, file.toPath(), StandardCopyOption.REPLACE_EXISTING);
                showAlert("Facture téléchargée avec succès!", Alert.AlertType.INFORMATION);
            }
        } catch (IOException e) {
            showAlert("Erreur lors du téléchargement: " + e.getMessage(), Alert.AlertType.ERROR);
        }
    }

    private void setupSorting() {
        try {
            // 1. Ajouter les options de tri au ComboBox
            sortComboBox.getItems().clear();
            sortComboBox.getItems().addAll(
                    "Nom médicament (A-Z)",
                    "Nom médicament (Z-A)",
                    "Date récente",
                    "Date ancienne"
            );

            // 2. Sélectionner une valeur par défaut
            if (!sortComboBox.getItems().isEmpty()) {
                sortComboBox.getSelectionModel().selectFirst();
            }

            // 3. Configurer le listener pour le tri dynamique
            sortComboBox.getSelectionModel().selectedItemProperty().addListener((obs, oldVal, newVal) -> {
                if (newVal != null) {
                    Comparator<Commande> comparator = null;

                    switch (newVal) {
                        case "Nom médicament (A-Z)":
                            comparator = Comparator.comparing(
                                    c -> c.getNomMedicamentsCommandes().toLowerCase(),
                                    Comparator.nullsLast(Comparator.naturalOrder())
                            );
                            break;

                        case "Nom médicament (Z-A)":
                            comparator = Comparator.comparing(
                                    c -> c.getNomMedicamentsCommandes().toLowerCase(),
                                    Comparator.nullsLast(Comparator.reverseOrder())
                            );
                            break;

                        case "Date récente":
                            comparator = Comparator.comparing(
                                    Commande::getDate_commande,
                                    Comparator.nullsLast(Comparator.reverseOrder())
                            );
                            break;

                        case "Date ancienne":
                            comparator = Comparator.comparing(
                                    Commande::getDate_commande,
                                    Comparator.nullsLast(Comparator.naturalOrder())
                            );
                            break;
                    }

                    if (comparator != null) {
                        FXCollections.sort(commandeData, comparator);
                        pagination.setPageCount(calculatePageCount());
                        updateTableForPage(pagination.getCurrentPageIndex());
                    }
                }
            });

        } catch (Exception e) {
            System.err.println("Erreur dans setupSorting: " + e.getMessage());
            e.printStackTrace();
        }
    }
    private void setupSearch() {
        filteredData = new FilteredList<>(commandeData, p -> true);

        searchField.textProperty().addListener((observable, oldValue, newValue) -> {
            filteredData.setPredicate(commande -> {
                if (newValue == null || newValue.isEmpty()) return true;

                String lowerCaseFilter = newValue.toLowerCase();
                return commande.getNomMedicamentsCommandes().toLowerCase().contains(lowerCaseFilter) ||
                        commande.getDate_commande().toString().contains(lowerCaseFilter);
            });

            pagination.setPageCount(calculatePageCount());
            updateTableForPage(pagination.getCurrentPageIndex()); // ✅ Nécessaire pour mettre à jour l'affichage
        });
    }

    private void setupPagination() {
        pagination.setPageCount(calculatePageCount());
        pagination.currentPageIndexProperty().addListener((obs, oldIndex, newIndex) -> {
            updateTableForPage(newIndex.intValue());
        });
        updateTableForPage(0); // Initialiser avec la première page
    }

    private void updateTableForPage(int pageIndex) {
        int fromIndex = pageIndex * ITEMS_PER_PAGE;
        int toIndex = Math.min(fromIndex + ITEMS_PER_PAGE, filteredData.size());

        if(fromIndex > filteredData.size() || fromIndex < 0) return;

        List<Commande> subList = new ArrayList<>(filteredData.subList(fromIndex, toIndex));
        commandeTable.setItems(FXCollections.observableArrayList(subList));
    }

    private int calculatePageCount() {
        return (int) Math.ceil((double) filteredData.size() / ITEMS_PER_PAGE);
    }

    private Node createPage(int pageIndex) {
        int fromIndex = pageIndex * ITEMS_PER_PAGE;
        int toIndex = Math.min(fromIndex + ITEMS_PER_PAGE, filteredData.size());

        commandeTable.setItems(FXCollections.observableArrayList(
                filteredData.subList(fromIndex, toIndex)
        ));

        return commandeTable;
    }


}




