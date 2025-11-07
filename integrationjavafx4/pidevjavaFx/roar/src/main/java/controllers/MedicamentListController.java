package controllers;

import entite.Medicament;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.chart.PieChart;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.stage.Stage;
import service.MedicamentService;

import java.io.IOException;
import java.time.LocalDate;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.stream.Collectors;

public class MedicamentListController {

    private final MedicamentService medicamentService = new MedicamentService();
    private final ObservableList<Medicament> medicamentData = FXCollections.observableArrayList();
    private FilteredList<Medicament> filteredData;
    @FXML private TableView<Medicament> medicamentTable;
    @FXML private TableColumn<Medicament, String> nameColumn;
    @FXML private TableColumn<Medicament, String> descriptionColumn;
    @FXML private TableColumn<Medicament, String> typeColumn;
    @FXML private TableColumn<Medicament, Integer> stockColumn;
    @FXML private TableColumn<Medicament, Double> prixColumn;
    @FXML private TableColumn<Medicament, String> dateEntreeColumn;
    @FXML private TableColumn<Medicament, String> dateExpirationColumn;
    @FXML private TableColumn<Medicament, Void> modifyColumn;
    @FXML private TableColumn<Medicament, Void> deleteColumn;
    @FXML private TextField searchField;
    @FXML private ComboBox<String> sortComboBox;
    @FXML private Pagination pagination;
    @FXML private ComboBox<Integer> itemsPerPageCombo;
    @FXML private PieChart typePieChart;
    @FXML private Label expirationAlertLabel;

    private ObservableList<Medicament> allMedicaments = FXCollections.observableArrayList();
    private ObservableList<Medicament> medicamentsProchesExpiration = FXCollections.observableArrayList();
    private static final int DEFAULT_ITEMS_PER_PAGE = 10;

    @FXML
    private void initialize() {
        configureTableColumns();
        addTableButtons();
        refreshTableData();
        filteredData = new FilteredList<>(medicamentData, p -> true);
        medicamentTable.setItems(filteredData);
        setupSearch();
        setupSorting();
        setupPagination();
        configureItemsPerPage();
        String css = ".table-view .scroll-bar:vertical, .table-view .scroll-bar:horizontal { -fx-opacity: 0; -fx-pref-width: 0; }";
        medicamentTable.setStyle(css);
        loadPieChartStats();
        highlightExpiringMedications();

    }

    private void configureTableColumns() {
        nameColumn.setCellValueFactory(new PropertyValueFactory<>("nom_medicament"));
        descriptionColumn.setCellValueFactory(new PropertyValueFactory<>("description_medicament"));
        typeColumn.setCellValueFactory(new PropertyValueFactory<>("type_medicament"));
        stockColumn.setCellValueFactory(new PropertyValueFactory<>("quantite_stock"));
        prixColumn.setCellValueFactory(new PropertyValueFactory<>("prix_medicament"));
        dateEntreeColumn.setCellValueFactory(new PropertyValueFactory<>("date_entree"));
        dateExpirationColumn.setCellValueFactory(new PropertyValueFactory<>("date_expiration"));
    }

    private void addTableButtons() {
        addModifyButtonToTable();
        addDeleteButtonToTable();
    }

    private void addModifyButtonToTable() {
        modifyColumn.setCellFactory(param -> new TableCell<>() {
            private final Button modifyBtn = new Button("Modify");

            {
                modifyBtn.setStyle("-fx-background-color: blue; -fx-text-fill: white;"); // Set the button color to blue with white text
                modifyBtn.setOnAction(e -> {
                    Medicament m = getTableView().getItems().get(getIndex());
                    handleModify(m);
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
            private final Button deleteBtn = new Button("Delete");

            {
                // Set the Delete button's style to red with white text
                deleteBtn.setStyle("-fx-background-color: red; -fx-text-fill: white;");
                deleteBtn.setOnAction(e -> {
                    Medicament m = getTableView().getItems().get(getIndex());
                    handleDeleteConfirmation(m);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : deleteBtn);
            }
        });
    }

    @FXML
    private void handleNewMedicament() {
        try {
            // Charger la nouvelle vue
            Parent root = FXMLLoader.load(getClass().getResource("/medicament.fxml"));
            Stage stage = (Stage) medicamentTable.getScene().getWindow();
            stage.setScene(new Scene(root));

            // Ajouter un listener pour quand la fenêtre se ferme
            stage.setOnHidden(e -> refreshTableData());

            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void handleModify(Medicament m) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/medicament_update.fxml"));
            Parent root = loader.load();

            // Get controller instance and inject the selected Medicament
            MedicamentUpdateController controller = loader.getController();
            controller.setMedicament(m);

            // Show new scene
            Stage stage = (Stage) medicamentTable.getScene().getWindow();
            stage.setScene(new Scene(root));
            stage.setOnHidden(e -> refreshTableData());
            stage.show();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    private void handleDeleteConfirmation(Medicament m) {
        Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
        alert.setTitle("Delete Confirmation");
        alert.setHeaderText("Delete " + m.getNom_medicament() + "?");
        alert.setContentText("This action cannot be undone.");

        Optional<ButtonType> result = alert.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            medicamentService.delete(m);
            refreshTableData();
        }
    }

    private void refreshTableData() {
        medicamentData.setAll(medicamentService.readAll());
        medicamentTable.setItems(filteredData);
        updatePieChart();
    }

    private void configureTable() {
        nameColumn.setCellValueFactory(new PropertyValueFactory<>("nom_medicament"));
        descriptionColumn.setCellValueFactory(new PropertyValueFactory<>("description_medicament"));
        typeColumn.setCellValueFactory(new PropertyValueFactory<>("type_medicament"));
        prixColumn.setCellValueFactory(new PropertyValueFactory<>("prix_medicament"));
        stockColumn.setCellValueFactory(new PropertyValueFactory<>("quantite_stock"));
        dateEntreeColumn.setCellValueFactory(new PropertyValueFactory<>("date_entree"));
        dateExpirationColumn.setCellValueFactory(new PropertyValueFactory<>("date_expiration"));

        medicamentData.setAll(medicamentService.readAll());
        filteredData = new FilteredList<>(medicamentData, p -> true);
    }

    private void setupSearch() {
        searchField.textProperty().addListener((obs, oldVal, newVal) -> {
            filteredData.setPredicate(medicament -> {
                if (newVal == null || newVal.isEmpty()) return true;
                return medicament.getNom_medicament().toLowerCase().contains(newVal.toLowerCase());
            });
            updatePagination();
        });
    }

    private void setupSorting() {
        sortComboBox.getItems().addAll(
                "Nom (A-Z)",
                "Nom (Z-A)",
                "Date entrée récente",
                "Date expiration proche"
        );

        sortComboBox.getSelectionModel().selectedItemProperty().addListener((obs, oldVal, newVal) -> {
            Comparator<Medicament> comparator = null;
            switch(newVal) {
                case "Nom (A-Z)":
                    comparator = Comparator.comparing(Medicament::getNom_medicament);
                    break;
                case "Nom (Z-A)":
                    comparator = Comparator.comparing(Medicament::getNom_medicament).reversed();
                    break;
                case "Date entrée récente":
                    comparator = Comparator.comparing(Medicament::getDate_entree).reversed();
                    break;
                case "Date expiration proche":
                    comparator = Comparator.comparing(Medicament::getDate_expiration);
                    break;
            }
            if (comparator != null) {
                FXCollections.sort(medicamentData, comparator);
            }
        });
    }

    private void setupPagination() {
        pagination.setPageCount(calculatePageCount());
        pagination.currentPageIndexProperty().addListener((obs, oldIndex, newIndex) -> {
            int itemsPerPage = getItemsPerPage(); // Conversion en int
            int from = newIndex.intValue() * itemsPerPage; // Maintenant int * int
            int to = Math.min(from + itemsPerPage, filteredData.size());
            medicamentTable.setItems(FXCollections.observableArrayList(filteredData.subList(from, to)));
        });
    }

    private void configureItemsPerPage() {
        itemsPerPageCombo.getItems().addAll(5, 10, 20, 50);
        itemsPerPageCombo.setValue(DEFAULT_ITEMS_PER_PAGE);
        itemsPerPageCombo.valueProperty().addListener((obs, oldVal, newVal) -> updatePagination());
    }

    private int getItemsPerPage() {
        return itemsPerPageCombo.getValue() != null ?
                itemsPerPageCombo.getValue().intValue() : // Conversion explicite en int
                DEFAULT_ITEMS_PER_PAGE;
    }

    private int calculatePageCount() {
        return (int) Math.ceil((double) filteredData.size() / getItemsPerPage());
    }

    private void updatePagination() {
        pagination.setPageCount(calculatePageCount());
        pagination.setCurrentPageIndex(0);
    }

    private void loadPieChartStats() {
        Map<String, Integer> stats = medicamentService.getTypeCounts();
        ObservableList<PieChart.Data> pieChartData = FXCollections.observableArrayList();

        for (Entry<String, Integer> entry : stats.entrySet()) {
            pieChartData.add(new PieChart.Data(entry.getKey(), entry.getValue()));
        }

        typePieChart.setData(pieChartData);
        typePieChart.setTitle("Types de Médicaments");
    }
    private void chargerMedicaments() {
        allMedicaments.setAll(medicamentService.readAll()); // Récupère tous les médicaments
        filtrerMedicamentsProchesExpiration();
    }

    private void filtrerMedicamentsProchesExpiration() {
        LocalDate today = LocalDate.now();
        LocalDate dans30Jours = today.plusDays(30);

        List<Medicament> filtrés = allMedicaments.stream()
                .filter(m -> {
                    LocalDate expiration = m.getDate_expiration();
                    return expiration != null && !expiration.isBefore(today) && !expiration.isAfter(dans30Jours);
                })
                .collect(Collectors.toList());

        medicamentsProchesExpiration.setAll(filtrés);
    }

    private void highlightExpiringMedications() {
        LocalDate today = LocalDate.now();
        LocalDate limitDate = today.plusDays(30);

        List<Medicament> expiringSoon = medicamentService.readAll().stream()
                .filter(m -> {
                    LocalDate expiration = m.getDate_expiration();
                    return expiration != null && !expiration.isBefore(today) && !expiration.isAfter(limitDate);
                })
                .collect(Collectors.toList());

        if (!expiringSoon.isEmpty()) {
            Alert alert = new Alert(Alert.AlertType.WARNING);
            alert.setTitle("Alerte d'expiration");
            alert.setHeaderText("Médicaments proches de l'expiration");
            String content = expiringSoon.stream()
                    .map(m -> "- " + m.getNom_medicament() + " (expire le " + m.getDate_expiration() + ")")
                    .collect(Collectors.joining("\n"));
            alert.setContentText(content);
            alert.show();
        }
    }
    private void updatePieChart() {
        // Calculer les nouvelles statistiques
        Map<String, Integer> stats = medicamentService.readAll().stream()
                .collect(Collectors.groupingBy(
                        Medicament::getType_medicament,
                        Collectors.summingInt(m -> 1)
                ));

        // Mettre à jour les données du PieChart
        ObservableList<PieChart.Data> pieChartData = FXCollections.observableArrayList();
        stats.forEach((type, count) ->
                pieChartData.add(new PieChart.Data(type + " (" + count + ")", count))
        );

        // Appliquer les nouvelles données
        typePieChart.setData(pieChartData);
    }

}
