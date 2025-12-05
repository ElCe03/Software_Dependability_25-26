package controllers;


import entite.reservation;
import entite.salle;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.*;
import service.ReservationService;
import service.SalleService;
import util.DataSource;
import util.EmailService;

import java.sql.*;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.util.logging.Level;
import java.util.logging.Logger;

public class ReservationDialogController {
    public static final Logger LOGGER = Logger.getLogger(ReservationDialogController.class.getName());
    private static final DateTimeFormatter DATE_TIME_FORMATTER = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");

    @FXML private TextField emailField;
    @FXML private DatePicker dateDebutPicker;
    @FXML private ComboBox<String> heureDebutCombo;
    @FXML private DatePicker dateFinPicker;
    @FXML private ComboBox<String> heureFinCombo;

    private salle selectedSalle;
    private Dialog<ButtonType> dialog;
    private final SalleService salleService = new SalleService();
    private final ReservationService reservationService = new ReservationService();

    @FXML
    public void initialize() {
        heureDebutCombo.setItems(FXCollections.observableArrayList(
                "08:00", "09:00", "10:00", "11:00", "12:00",
                "13:00", "14:00", "15:00", "16:00", "17:00", "18:00"
        ));
        heureFinCombo.setItems(FXCollections.observableArrayList(
                "08:00", "09:00", "10:00", "11:00", "12:00",
                "13:00", "14:00", "15:00", "16:00", "17:00", "18:00"
        ));
    }

    public void setDialog(Dialog<ButtonType> dialog) {
        this.dialog = dialog;
        dialog.getDialogPane().lookupButton(ButtonType.OK).addEventFilter(ActionEvent.ACTION, event -> {
            if (!validateInputs()) {
                event.consume();
            } else {
                handleReservation();
            }
        });
    }

    public void setSalle(salle salle) {
        this.selectedSalle = salle;
        LOGGER.info("Salle sélectionnée: " + (salle != null ? salle.getId() + " - " + salle.getNom() : "null"));
    }

    private boolean validateInputs() {
        if (emailField.getText().isEmpty() ||
                dateDebutPicker.getValue() == null ||
                heureDebutCombo.getValue() == null ||
                dateFinPicker.getValue() == null ||
                heureFinCombo.getValue() == null) {
            showAlert("Erreur", "Veuillez remplir tous les champs", Alert.AlertType.ERROR);
            return false;
        }

        if (!isValidEmail(emailField.getText())) {
            showAlert("Erreur", "Veuillez entrer une adresse email valide", Alert.AlertType.ERROR);
            return false;
        }

        LocalDateTime debut = getDateTime(dateDebutPicker.getValue(), heureDebutCombo.getValue());
        LocalDateTime fin = getDateTime(dateFinPicker.getValue(), heureFinCombo.getValue());

        if (fin.isBefore(debut)) {
            showAlert("Erreur", "La date de fin doit être postérieure à la date de début", Alert.AlertType.ERROR);
            return false;
        }

        if (fin.isEqual(debut)) {
            showAlert("Erreur", "La durée de réservation doit être d'au moins une minute", Alert.AlertType.ERROR);
            return false;
        }

        try {
            if (!salleService.isSalleAvailable(selectedSalle.getId(), debut, fin)) {
                showAlert("Erreur", "La salle est déjà réservée pour cette période", Alert.AlertType.ERROR);
                return false;
            }
        } catch (SQLException e) {
            LOGGER.log(Level.SEVERE, "Erreur lors de la vérification de disponibilité", e);
            showAlert("Erreur", "Erreur lors de la vérification de disponibilité: " + e.getMessage(), Alert.AlertType.ERROR);
            return false;
        }

        return true;
    }

    private boolean isValidEmail(String email) {
        return email != null && email.matches("^[\\w-.]+@([\\w-]+\\.)+[\\w-]{2,4}$");
    }

    private LocalDateTime getDateTime(LocalDate date, String heure) {
        LocalTime time = LocalTime.parse(heure);
        return LocalDateTime.of(date, time);
    }

    private void handleReservation() {
        try (Connection conn = DataSource.getInstance().getConnection()) {
            conn.setAutoCommit(false);

            try {
                LOGGER.info("Début de la transaction de réservation...");

                LocalDateTime dateDebut = getDateTime(dateDebutPicker.getValue(), heureDebutCombo.getValue());
                LocalDateTime dateFin = getDateTime(dateFinPicker.getValue(), heureFinCombo.getValue());

                reservation res = new reservation();
                res.setSalle(selectedSalle);
                res.setDate_debut(Timestamp.valueOf(dateDebut));
                res.setDate_fin(Timestamp.valueOf(dateFin));

                LOGGER.info("Tentative d'ajout de réservation...");
                reservationService.addReservation(conn, res);
                LOGGER.info("Réservation ajoutée avec ID: " + res.getId());

                LOGGER.info("Mise à jour du statut de la salle...");
                selectedSalle.setStatus("Occupée");
                salleService.updateSalle(conn, selectedSalle);

                conn.commit();
                LOGGER.info("Transaction confirmée avec succès");

                // Envoyer les emails
                String formattedDateDebut = dateDebut.format(DATE_TIME_FORMATTER);
                String formattedDateFin = dateFin.format(DATE_TIME_FORMATTER);
                String recipientEmail = emailField.getText();
                String adminEmail = "eyah5268@gmail.com";

                LOGGER.info("Envoi des emails de confirmation...");
                sendEmail(recipientEmail, formattedDateDebut, formattedDateFin);
                sendEmail(adminEmail, formattedDateDebut, formattedDateFin);

                showAlert("Succès", "Réservation effectuée avec succès. Un email de confirmation a été envoyé.", Alert.AlertType.INFORMATION);
                dialog.setResult(ButtonType.OK);
                dialog.close();

            } catch (SQLException e) {
                conn.rollback();
                LOGGER.log(Level.SEVERE, "Erreur lors de la réservation - Transaction annulée", e);
                showAlert("Erreur", "Échec de la réservation: " + e.getMessage(), Alert.AlertType.ERROR);
            } finally {
                try {
                    conn.setAutoCommit(true);
                } catch (SQLException e) {
                    LOGGER.log(Level.SEVERE, "Erreur lors du rétablissement de l'auto-commit", e);
                }
            }
        } catch (SQLException e) {
            LOGGER.log(Level.SEVERE, "Erreur de connexion à la base de données", e);
            showAlert("Erreur", "Erreur de connexion à la base de données: " + e.getMessage(), Alert.AlertType.ERROR);
        }
    }

    private void sendEmail(String toEmail, String dateDebut, String dateFin) {
        LOGGER.info("Envoi d'email à: " + toEmail);
        EmailService.sendReservationEmail(
                toEmail,
                selectedSalle.getNom(),
                dateDebut,
                dateFin,
                selectedSalle.getType_salle(),
                selectedSalle.getStatus(),
                () -> LOGGER.info("Email envoyé avec succès à " + toEmail),
                () -> LOGGER.warning("Échec d'envoi à " + toEmail)
        );
    }

    private void showAlert(String title, String message, Alert.AlertType type) {
        Platform.runLater(() -> {
            Alert alert = new Alert(type);
            alert.setTitle(title);
            alert.setHeaderText(null);
            alert.setContentText(message);
            alert.showAndWait();
  });
}
}