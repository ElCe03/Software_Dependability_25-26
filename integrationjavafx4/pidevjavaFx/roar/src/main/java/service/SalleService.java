package service;

import entite.etage;
import entite.salle;
import util.DataSource;

import java.sql.*;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static controllers.ReservationDialogController.LOGGER;
import static java.sql.DriverManager.getConnection;

public class SalleService {

    public void addSalle(salle s) {
        String query = "INSERT INTO salle (nom, capacite, type_salle, status, etage_id, image, priorite) VALUES (?, ?, ?, ?, ?, ?, ?)";
        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query, Statement.RETURN_GENERATED_KEYS)) {

            ps.setString(1, s.getNom());
            ps.setInt(2, s.getCapacite());
            ps.setString(3, s.getType_salle());
            ps.setString(4, s.getStatus());
            ps.setInt(5, s.getEtage().getId());
            ps.setString(6, s.getImage());
            ps.setInt(7, s.getPriorite());

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    s.setId(rs.getInt(1));
                }
            }

            // Increment nbr_salle for the associated etage
            etage etage = s.getEtage();
            etage.setNbrSalle(etage.getNbrSalle() + 1);

        } catch (SQLException e) {
            System.err.println("Error adding salle: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to add salle", e);
        }
    }

    public List<salle> getAll() {
        List<salle> list = new ArrayList<salle>();
        String query = "SELECT s.*, e.numero as etage_numero FROM salle s LEFT JOIN etage e ON s.etage_id = e.id";

        try (Connection conn = DataSource.getInstance().getConnection();
             Statement stmt = conn.createStatement();
             ResultSet rs = stmt.executeQuery(query)) {

            while (rs.next()) {
                salle s = new salle();
                s.setId(rs.getInt("id"));
                s.setNom(rs.getString("nom"));
                s.setCapacite(rs.getInt("capacite"));
                s.setType_salle(rs.getString("type_salle"));
                s.setStatus(rs.getString("status"));
                s.setImage(rs.getString("image"));
                s.setPriorite(rs.getInt("priorite"));

                etage e = new etage();
                e.setId(rs.getInt("etage_id"));
                e.setNumero(rs.getInt("etage_numero"));
                s.setEtage(e);

                list.add(s);
            }
        } catch (SQLException e) {
            System.err.println("Error fetching salles: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to fetch salles", e);
        }
        return list;
    }

    public void updateSalle(Connection conn, salle s) throws SQLException {
        // Retrieve the current etage_id to detect if etage changes
        String selectQuery = "SELECT etage_id FROM salle WHERE id = ?";
        int oldEtageId = -1;
        try (PreparedStatement ps = conn.prepareStatement(selectQuery)) {
            ps.setInt(1, s.getId());
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    oldEtageId = rs.getInt("etage_id");
                }
            }
        }

        // Update the salle
        String query = "UPDATE salle SET nom = ?, capacite = ?, type_salle = ?, status = ?, etage_id = ?, image = ?, priorite = ? WHERE id = ?";
        try (PreparedStatement ps = conn.prepareStatement(query)) {
            ps.setString(1, s.getNom());
            ps.setInt(2, s.getCapacite());
            ps.setString(3, s.getType_salle());
            ps.setString(4, s.getStatus());
            ps.setInt(5, s.getEtage().getId());
            ps.setString(6, s.getImage());
            ps.setInt(7, s.getPriorite());
            ps.setInt(8, s.getId());

            int rowsAffected = ps.executeUpdate();
            if (rowsAffected == 0) {
                throw new SQLException("No rows updated for salle id: " + s.getId());
            }

            // Update nbr_salle if etage changed
            if (oldEtageId != s.getEtage().getId()) {
                // Decrement nbr_salle for old etage
                if (oldEtageId != -1) {
                    String updateOldEtageQuery = "UPDATE etage SET nbr_salle = nbr_salle - 1 WHERE id = ?";
                    try (PreparedStatement psEtage = conn.prepareStatement(updateOldEtageQuery)) {
                        psEtage.setInt(1, oldEtageId);
                        psEtage.executeUpdate();
                    }
                }
                // Increment nbr_salle for new etage
                String updateNewEtageQuery = "UPDATE etage SET nbr_salle = nbr_salle + 1 WHERE id = ?";
                try (PreparedStatement psEtage = conn.prepareStatement(updateNewEtageQuery)) {
                    psEtage.setInt(1, s.getEtage().getId());
                    psEtage.executeUpdate();
                }
            }
        }
    }
    public void updateSalle(salle s) {
        try (Connection conn = DataSource.getInstance().getConnection()) {
            updateSalle(conn, s);
        } catch (SQLException e) {
            throw new RuntimeException("Échec de la mise à jour de la salle", e);
        }
    }

    public void deleteSalle(int id) {
        // Retrieve the etage_id before deleting
        String selectQuery = "SELECT etage_id FROM salle WHERE id = ?";
        int etageId = -1;
        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(selectQuery)) {
            ps.setInt(1, id);
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    etageId = rs.getInt("etage_id");
                }
            }
        } catch (SQLException e) {
            System.err.println("Error fetching etage_id: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to fetch etage_id", e);
        }

        // Delete the salle
        String query = "DELETE FROM salle WHERE id = ?";
        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query)) {

            ps.setInt(1, id);
            ps.executeUpdate();

            // Decrement nbr_salle for the associated etage
            if (etageId != -1) {
                etage etage = getEtageById(etageId);
                if (etage != null) {
                    etage.setNbrSalle(etage.getNbrSalle() - 1);
                }
            }

        } catch (SQLException e) {
            System.err.println("Error deleting salle: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to delete salle", e);
        }
    }

    public List<salle> getSallesByEtage(int etageId) {
        List<salle> list = new ArrayList<salle>();
        String query = "SELECT s.*, e.numero as etage_numero FROM salle s LEFT JOIN etage e ON s.etage_id = e.id WHERE s.etage_id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query)) {

            ps.setInt(1, etageId);

            try (ResultSet rs = ps.executeQuery()) {
                while (rs.next()) {
                    salle s = new salle();
                    s.setId(rs.getInt("id"));
                    s.setNom(rs.getString("nom"));
                    s.setCapacite(rs.getInt("capacite"));
                    s.setType_salle(rs.getString("type_salle"));
                    s.setStatus(rs.getString("status"));
                    s.setImage(rs.getString("image"));
                    s.setPriorite(rs.getInt("priorite"));

                    etage e = new etage();
                    e.setId(rs.getInt("etage_id"));
                    e.setNumero(rs.getInt("etage_numero"));
                    s.setEtage(e);

                    list.add(s);
                }
            }
        } catch (SQLException e) {
            System.err.println("Error fetching salles by etage: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to fetch salles by etage", e);
        }
        return list;
    }

    public int countSallesByEtage(int etageId) {
        String query = "SELECT COUNT(*) FROM salle WHERE etage_id = ?";
        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query)) {
            ps.setInt(1, etageId);
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    return rs.getInt(1);
                }
            }
        } catch (SQLException e) {
            System.err.println("Error counting salles by etage: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException("Failed to count salles by etage", e);
        }
        return 0;
    }

    public etage getEtageById(int etageId) {
        return EtageService.getEtageById(etageId);
    }
    public void updateSalleStatus(int salleId, String newStatus) throws SQLException {
        String query = "UPDATE salle SET status = ? WHERE id = ?";
        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement stmt = conn.prepareStatement(query)) {
            stmt.setString(1, newStatus);
            stmt.setInt(2, salleId);
            stmt.executeUpdate();
        }
    }
    public boolean isSalleAvailable(int salleId, LocalDateTime start, LocalDateTime end) throws SQLException {
        String query = "SELECT COUNT(*) FROM reservation WHERE salle_id = ? " +
                "AND ((date_debut < ? AND date_fin > ?) OR " +
                "(date_debut BETWEEN ? AND ?) OR " +
                "(date_fin BETWEEN ? AND ?))";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query)) {

            Timestamp startTs = Timestamp.valueOf(start);
            Timestamp endTs = Timestamp.valueOf(end);

            ps.setInt(1, salleId);
            ps.setTimestamp(2, endTs);
            ps.setTimestamp(3, startTs);
            ps.setTimestamp(4, startTs);
            ps.setTimestamp(5, endTs);
            ps.setTimestamp(6, startTs);
            ps.setTimestamp(7, endTs);

            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    int count = rs.getInt(1);
                    LOGGER.info("Availability check for salle " + salleId + ": " + count + " conflicts found");
                    return count == 0;
                }
            }
        }
        return true;
    }
    public void updateSalleStatus(Connection conn, int salleId, String newStatus) throws SQLException {
        String query = "UPDATE salle SET status = ? WHERE id = ?";
        try (PreparedStatement stmt = conn.prepareStatement(query)) {
            stmt.setString(1, newStatus);
            stmt.setInt(2, salleId);
            stmt.executeUpdate();
        }
    }
    public List<salle> getAvailableSalles() throws SQLException {
        List<salle> availableSalles = new ArrayList<salle>();
        String query = "SELECT * FROM salle WHERE status = 'Disponible'";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement ps = conn.prepareStatement(query);
             ResultSet rs = ps.executeQuery()) {

            while (rs.next()) {
                salle s = new salle();
                s.setId(rs.getInt("id"));
                s.setNom(rs.getString("nom"));
                s.setCapacite(rs.getInt("capacite"));
                s.setType_salle(rs.getString("type_salle"));
                s.setStatus(rs.getString("status"));
                s.setImage(rs.getString("image"));
                s.setPriorite(rs.getInt("priorite"));

                // Si vous avez besoin des informations d'étage
                etage e = new etage();
                e.setId(rs.getInt("etage_id"));
                s.setEtage(e);

                availableSalles.add(s);
            }
        }
        return availableSalles;
}

}