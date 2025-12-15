package service;

import entite.reservation;
import entite.salle;
import util.DataSource;
import java.sql.*;
import java.util.ArrayList;
import java.util.List;

import static controllers.ReservationDialogController.LOGGER;

public class ReservationService {

    public void addReservation(Connection conn, reservation reservation) throws SQLException {
        String query = "INSERT INTO reservation (salle_id, date_debut, date_fin) VALUES (?, ?, ?)";
        try (PreparedStatement ps = conn.prepareStatement(query, Statement.RETURN_GENERATED_KEYS)) {
            ps.setInt(1, reservation.getSalle().getId());
            ps.setTimestamp(2, reservation.getDate_debut());
            ps.setTimestamp(3, reservation.getDate_fin());

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    reservation.setId(rs.getInt(1));
                }
            }
        }
    }

    public List<reservation> getReservationsForSalle(int salleId) throws SQLException {
        List<reservation> reservations = new ArrayList<>();
        String query = "SELECT * FROM reservation WHERE salle_id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query)) {
            ps.setInt(1, salleId);

            try (ResultSet rs = ps.executeQuery()) {
                while (rs.next()) {
                    reservation res = new reservation();
                    res.setId(rs.getInt("id"));
                    res.setDate_debut(rs.getTimestamp("date_debut"));
                    res.setDate_fin(rs.getTimestamp("date_fin"));
                    // You'll need to set the Salle object here
                    reservations.add(res);
                }
            }
        }
        return reservations;
    }

    public void terminerReservation(Connection conn, int reservationId) throws SQLException {
        // Requête pour libérer la salle
        String updateSalleQuery = "UPDATE salle s JOIN reservation r ON s.id = r.salle_id " +
                "SET s.status = 'Libre' WHERE r.id = ?";

        // Requête pour supprimer la réservation
        String deleteReservationQuery = "DELETE FROM reservation WHERE id = ?";

        try {
            conn.setAutoCommit(false);
            LOGGER.info("Début de la transaction pour terminer la réservation");

            try (PreparedStatement psSalle = conn.prepareStatement(updateSalleQuery);
                 PreparedStatement psReservation = conn.prepareStatement(deleteReservationQuery)) {

                // 1. Libérer la salle
                psSalle.setInt(1, reservationId);
                int salleUpdated = psSalle.executeUpdate();
                LOGGER.info(salleUpdated + " salle(s) mise(s) à jour");

                // 2. Supprimer la réservation
                psReservation.setInt(1, reservationId);
                int reservationDeleted = psReservation.executeUpdate();
                LOGGER.info(reservationDeleted + " réservation(s) supprimée(s)");

                conn.commit();
                LOGGER.info("Transaction confirmée - Réservation terminée avec succès");
            }
        } catch (SQLException e) {
            try {
                if (conn != null) {
                    conn.rollback();
                    LOGGER.info("Transaction annulée");
                }
            } catch (SQLException ex) {
                LOGGER.severe("Erreur lors de l'annulation: " + ex.getMessage());
            }
            LOGGER.severe("Erreur lors de la terminaison de la réservation: " + e.getMessage());
            throw e;
        } finally {
            try {
                if (conn != null) {
                    conn.setAutoCommit(true);
                }
            } catch (SQLException e) {
                LOGGER.warning("Erreur lors du rétablissement de l'auto-commit: " + e.getMessage());
            }
        }
    }

    public List<reservation> getAllReservations() throws SQLException {
        List<reservation> reservations = new ArrayList<>();
        String query = "SELECT r.id, r.salle_id, r.date_debut, r.date_fin, " +
                "s.nom as salle_nom, s.status as salle_status, s.capacite, s.type_salle " +
                "FROM reservation r JOIN salle s ON r.salle_id = s.id " +
                "ORDER BY r.date_debut DESC";

        LOGGER.info("Exécution de la requête pour obtenir toutes les réservations");

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query);
             ResultSet rs = ps.executeQuery()) {

            while (rs.next()) {
                reservation res = new reservation();
                res.setId(rs.getInt("id"));

                // Création de l'objet Salle avec toutes les informations nécessaires
                salle salle = new salle();
                salle.setId(rs.getInt("salle_id"));
                salle.setNom(rs.getString("salle_nom"));
                salle.setStatus(rs.getString("salle_status"));
                salle.setCapacite(rs.getInt("capacite"));
                salle.setType_salle(rs.getString("type_salle"));

                res.setSalle(salle);
                res.setDate_debut(rs.getTimestamp("date_debut"));
                res.setDate_fin(rs.getTimestamp("date_fin"));

                reservations.add(res);
            }

            LOGGER.info(reservations.size() + " réservations récupérées avec succès");
        } catch (SQLException e) {
            LOGGER.severe("Erreur lors de la récupération des réservations: " + e.getMessage());
            throw e;
        }

        return reservations;
    }
    public void terminerReservation(int reservationId) throws SQLException {
        try (Connection conn = DataSource.getInstance().getConnection()) {
            conn.setAutoCommit(false);
            try {
                terminerReservation(conn, reservationId);
                conn.commit();
            } catch (SQLException e) {
                conn.rollback();
                throw e;
            }
  }
}

}