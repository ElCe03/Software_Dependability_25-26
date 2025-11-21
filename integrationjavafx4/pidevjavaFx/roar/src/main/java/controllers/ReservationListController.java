package controllers;

import entite.reservation;
import entite.salle;
import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.stage.Stage;
import service.ReservationService;

import java.io.IOException;
import java.net.URL;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

public class ReservationListController {

    @FXML private TableView<reservation> reservationTable;
    @FXML private TableColumn<reservation, Integer> idColumn;
    @FXML private TableColumn<reservation, String> salleColumn;
    @FXML private TableColumn<reservation, Timestamp> dateDebutColumn;
    @FXML private TableColumn<reservation, Timestamp> dateFinColumn;
    @FXML private TableColumn<reservation, String> statusColumn;
    @FXML private TableColumn<reservation, Void> actionColumn;
    @FXML private TextField searchField;

    //@ public invariant reservationData != null;
    private final ObservableList<reservation> reservationData = FXCollections.observableArrayList();
    //@ public invariant reservationService != null;
    private final ReservationService reservationService = new ReservationService();
    //@ public invariant dateFormatter != null;
    private final DateTimeFormatter dateFormatter = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");

    /*@ public normal_behavior
      @   requires reservationTable != null && idColumn != null && salleColumn != null &&
      @            dateDebutColumn != null && dateFinColumn != null && statusColumn != null &&
      @            actionColumn != null && searchField != null;
      @
      @   assignable idColumn.cellValueFactory, salleColumn.cellValueFactory,
      @              dateDebutColumn.cellValueFactory, dateDebutColumn.cellFactory,
      @              dateFinColumn.cellValueFactory, dateFinColumn.cellFactory,
      @              statusColumn.cellValueFactory, actionColumn.cellFactory,
      @              reservationData.content, reservationTable.items;
      @
      @   ensures idColumn.getCellValueFactory() != null;
      @   ensures salleColumn.getCellValueFactory() != null;
      @   ensures actionColumn.getCellFactory() != null;
      @   ensures reservationTable.getItems() == reservationData;
      @*/
    @FXML
    public void initialize() {
        System.out.println("Initialisation de ReservationListController...");
        configureTableColumns();
        loadReservations();
        debugTableViewContent();
    }

    /*@ private normal_behavior
      @   requires idColumn != null && salleColumn != null && dateDebutColumn != null &&
      @            dateFinColumn != null && statusColumn != null && actionColumn != null;
      @
      @   assignable idColumn.cellValueFactory, salleColumn.cellValueFactory,
      @              dateDebutColumn.cellValueFactory, dateDebutColumn.cellFactory,
      @              dateFinColumn.cellValueFactory, dateFinColumn.cellFactory,
      @              statusColumn.cellValueFactory, actionColumn.cellFactory;
      @
      @   ensures idColumn.getCellValueFactory() != null;
      @   ensures salleColumn.getCellValueFactory() != null;
      @   ensures dateDebutColumn.getCellFactory() != null;
      @   ensures dateFinColumn.getCellFactory() != null;
      @   ensures statusColumn.getCellValueFactory() != null;
      @   ensures actionColumn.getCellFactory() != null;
      @*/
    private void configureTableColumns() {
        idColumn.setCellValueFactory(new PropertyValueFactory<>("id"));

        salleColumn.setCellValueFactory(cellData ->
                new SimpleStringProperty(cellData.getValue().getSalle().getNom()));

        configureDateColumn(dateDebutColumn, "date_debut");
        configureDateColumn(dateFinColumn, "date_fin");

        statusColumn.setCellValueFactory(cellData ->
                new SimpleStringProperty(cellData.getValue().getSalle().getStatus()));

        actionColumn.setCellFactory(param -> new TableCell<>() {
            private final Button terminerBtn = new Button("Terminer");

            {
                terminerBtn.getStyleClass().addAll("btn", "btn-primary");
                terminerBtn.setOnAction(event -> {
                    reservation res = getTableView().getItems().get(getIndex());
                    terminerReservation(res);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                if (empty) {
                    setGraphic(null);
                } else {
                    reservation res = getTableView().getItems().get(getIndex());
                    terminerBtn.setDisable(!isReservationTerminable(res));
                    setGraphic(terminerBtn);
                }            
            }
        });

        System.out.println("Colonnes configurées : " + reservationTable.getColumns().size());
    }

    private boolean isReservationTerminable(reservation res) {
        return res.getDate_fin().toLocalDateTime().isBefore(LocalDateTime.now());
    }

    /*@ private normal_behavior
      @   requires column != null && propertyName != null;
      @   assignable column.cellValueFactory, column.cellFactory;
      @   ensures column.getCellValueFactory() != null;
      @   ensures column.getCellFactory() != null;
      @*/
    private void configureDateColumn(TableColumn<reservation, Timestamp> column, String propertyName) {
        column.setCellValueFactory(new PropertyValueFactory<>(propertyName));
        column.setCellFactory(col -> new TableCell<>() {
            @Override
            protected void updateItem(Timestamp item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                } else {
                    setText(dateFormatter.format(item.toLocalDateTime()));
                }
            }
        });
    }

    /*@ private normal_behavior
      @   requires reservationTable != null && reservationData != null && reservationService != null;
      @   assignable reservationData.content, reservationTable.items;
      @   ensures reservationTable.getItems() == reservationData;
      @*/
    private void loadReservations() {
        try {
            System.out.println("Chargement des réservations...");
            reservationData.clear();

            // Données factices pour tester
            reservation testRes = new reservation();
            testRes.setId(1);
            testRes.setDate_debut(Timestamp.valueOf(LocalDateTime.now()));
            testRes.setDate_fin(Timestamp.valueOf(LocalDateTime.now().plusHours(2)));
            salle testSalle = new salle(1, "Salle Test", "Disponible");
            testRes.setSalle(testSalle);
            reservationData.add(testRes);

            // Charger les données réelles
            reservationData.addAll(reservationService.getAllReservations());
            reservationTable.setItems(reservationData);
            System.out.println("Réservations chargées avec succès. Taille : " + reservationData.size());
        } catch (SQLException e) {
            System.err.println("Erreur lors du chargement des réservations : " + e.getMessage());
            e.printStackTrace();
            showAlert("Erreur", "Erreur lors du chargement: " + e.getMessage());
        }
    }

    private void debugTableViewContent() {
        System.out.println("Contenu de la TableView :");
        System.out.println("Nombre de réservations : " + reservationData.size());
        reservationData.forEach(res ->
                System.out.println("Réservation: ID=" + res.getId() + ", Salle=" + res.getSalle().getNom() +
                        ", Début=" + res.getDate_debut() + ", Fin=" + res.getDate_fin()));
        System.out.println("Colonnes du TableView : " + reservationTable.getColumns());
        System.out.println("TableView visible : " + reservationTable.isVisible());
    }

    /*@ private normal_behavior
      @   requires res != null && reservationService != null;
      @   assignable \everything;
      @*/
    private void terminerReservation(reservation res) {
        try {
            reservationService.terminerReservation(res.getId());
            loadReservations();
            showAlert("Succès", "Réservation terminée");
        } catch (SQLException e) {
            showAlert("Erreur", "Échec de la mise à jour: " + e.getMessage());
        }
    }

    /*@ public normal_behavior
      @   requires event != null && event.getSource() instanceof Node;
      @   assignable \everything;
      @*/
    @FXML
    private void showDepartements(ActionEvent event) {
        loadView("/departement.fxml", event);
    }

    /*@ public normal_behavior
      @   requires event != null && event.getSource() instanceof Node;
      @   assignable \everything;
      @*/
    @FXML
    private void showEtages(ActionEvent event) {
        loadView("/etage.fxml", event);
    }

    /*@ public normal_behavior
      @   assignable \nothing; // Non fa nulla
      @*/
    @FXML
    private void showReservation(ActionEvent event) {
        // Already on this view
    }

    /*@ private normal_behavior
      @   requires fxmlPath != null && event != null && event.getSource() instanceof Node;
      @   assignable \everything;
      @*/
    private void loadView(String fxmlPath, ActionEvent event) {
        try {
            URL url = getClass().getResource(fxmlPath);
            if (url == null) {
                throw new IOException("Fichier FXML introuvable: " + fxmlPath);
            }

            Parent root = FXMLLoader.load(url);
            Stage stage = (Stage)((Node)event.getSource()).getScene().getWindow();
            Scene scene = new Scene(root);
            scene.getStylesheets().add(getClass().getResource("/styles1.css").toExternalForm());
            stage.setScene(scene);
            stage.show();
        } catch (IOException e) {
            showAlert("Erreur", "Impossible de charger la vue: " + e.getMessage());
            e.printStackTrace();
        }
    }

    /*@ private normal_behavior
      @   requires title != null && message != null;
      @   assignable \nothing;
      @*/
    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.ERROR);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}