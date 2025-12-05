package controllers;

import entite.salle;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import service.SalleService;

import java.io.IOException;
import java.sql.SQLException;
import java.util.Optional;
import java.util.logging.Logger;

import javafx.fxml.FXMLLoader;

public class SalleDisponibleController {
    private static final Logger LOGGER = Logger.getLogger(SalleDisponibleController.class.getName());

    @FXML private TableView<salle> salleTable;
    @FXML private TableColumn<salle, Integer> idCol;
    @FXML private TableColumn<salle, String> nomCol;
    @FXML private TableColumn<salle, Integer> capaciteCol;
    @FXML private TableColumn<salle, String> typeCol;
    @FXML private TableColumn<salle, String> statusCol;
    @FXML private TableColumn<salle, Void> actionCol;

    private final ObservableList<salle> salleData = FXCollections.observableArrayList();
    private final SalleService salleService = new SalleService();

    @FXML
    public void initialize() {
        configureTableColumns();
        loadSalles();
    }

    private void configureTableColumns() {
        idCol.setCellValueFactory(new PropertyValueFactory<>("id"));
        nomCol.setCellValueFactory(new PropertyValueFactory<>("nom"));
        capaciteCol.setCellValueFactory(new PropertyValueFactory<>("capacite"));
        typeCol.setCellValueFactory(new PropertyValueFactory<>("type_salle"));
        statusCol.setCellValueFactory(new PropertyValueFactory<>("status"));

        // Configuration de la colonne d'action avec un bouton
        actionCol.setCellFactory(param -> new TableCell<>() {
            private final Button reserveButton = new Button();
            {
                // Tentative de chargement de l'icône
                Image reserveIcon = null;
                try {
                    reserveIcon = new Image(getClass().getResourceAsStream("/icons/reserve.png"));
                    ImageView iconView = new ImageView(reserveIcon);
                    iconView.setFitHeight(16);
                    iconView.setFitWidth(16);
                    reserveButton.setGraphic(iconView);
                    reserveButton.getStyleClass().add("icon-button");
                } catch (Exception e) {
                    LOGGER.warning("Impossible de charger l'icône /icons/reserve.png: " + e.getMessage());
                    // Fallback : utiliser un texte si l'icône est introuvable
                    reserveButton.setText("Réserver");
                    reserveButton.getStyleClass().add("text-button");
                }

                reserveButton.setOnAction(event -> {
                    salle selectedSalle = getTableView().getItems().get(getIndex());
                    showReservationDialog(selectedSalle);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : reserveButton);
            }
        });
    }

    private void loadSalles() {
        try {
            salleData.clear();
            // Charger uniquement les salles avec statut "Disponible"
            salleData.addAll(salleService.getAvailableSalles());
            salleTable.setItems(salleData);
            LOGGER.info("Salles disponibles chargées : " + salleData.size());
        } catch (SQLException e) {
            LOGGER.severe("Erreur lors du chargement des salles : " + e.getMessage());
            showAlert("Erreur", "Impossible de charger les salles : " + e.getMessage(), Alert.AlertType.ERROR);
        }
    }

    private void showReservationDialog(salle selectedSalle) {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/reservationDialog.fxml"));
            DialogPane dialogPane = loader.load();
            ReservationDialogController controller = loader.getController();
            if (controller == null) {
                showAlert("Erreur", "Controller non chargé pour reservationDialog.fxml", Alert.AlertType.ERROR);
                return;
            }
            controller.setSalle(selectedSalle);

            Dialog<ButtonType> dialog = new Dialog<>();
            dialog.setDialogPane(dialogPane);
            dialog.setTitle("Réserver Salle");

            // Pass the dialog to the controller
            controller.setDialog(dialog);

            Optional<ButtonType> result = dialog.showAndWait();
            if (result.isPresent() && result.get() == ButtonType.OK) {
                loadSalles(); // Refresh the TableView
            }
        } catch (IOException e) {
            LOGGER.severe("Erreur lors de l'ouverture de la fenêtre de réservation: " + e.getMessage());
            showAlert("Erreur", "Erreur lors de l'ouverture de la fenêtre de réservation: " + e.getMessage(), Alert.AlertType.ERROR);
        }
    }

    private void showAlert(String title, String message, Alert.AlertType alertType) {
        Alert alert = new Alert(alertType);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}