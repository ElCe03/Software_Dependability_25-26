package service;

import entite.reservation;
import entite.salle;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import util.DataSource;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.Timestamp;
import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class ReservationServiceETest {

    private ReservationService service;
    private int salleId;
    private int reservationId;

    @BeforeEach
    void setup() throws Exception {
        service = new ReservationService();
        Connection conn = DataSource.getInstance().getConnection();

        // ✅ 1. Create SALLE
        try (PreparedStatement ps = conn.prepareStatement(
                "INSERT INTO salle (nom, status, capacite, type_salle) VALUES (?, ?, ?, ?)",
                PreparedStatement.RETURN_GENERATED_KEYS)) {

            ps.setString(1, "Salle Test");
            ps.setString(2, "Occupée");
            ps.setInt(3, 20);
            ps.setString(4, "Réunion");

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    salleId = rs.getInt(1);
                }
            }
        }

        assertTrue(salleId > 0);

        // ✅ 2. Create RESERVATION
        reservation r = new reservation();
        salle s = new salle();
        s.setId(salleId);

        r.setSalle(s);
        r.setDate_debut(Timestamp.valueOf(LocalDateTime.now()));
        r.setDate_fin(Timestamp.valueOf(LocalDateTime.now().plusHours(2)));

        service.addReservation(conn, r);
        reservationId = r.getId();

        assertTrue(reservationId > 0);
    }

    @Test
    void testGetReservationsForSalle() throws Exception {
        List<reservation> list = service.getReservationsForSalle(salleId);
        assertNotNull(list);
        assertFalse(list.isEmpty());
    }

    @Test
    void testGetAllReservations() throws Exception {
        List<reservation> list = service.getAllReservations();
        assertNotNull(list);
        assertFalse(list.isEmpty());
    }

    @Test
    void testTerminerReservation() throws Exception {
        Connection conn = DataSource.getInstance().getConnection();

        service.terminerReservation(conn, reservationId);

        // ✅ Verify reservation deleted
        try (PreparedStatement ps = conn.prepareStatement(
                "SELECT * FROM reservation WHERE id = ?")) {

            ps.setInt(1, reservationId);
            try (ResultSet rs = ps.executeQuery()) {
                assertFalse(rs.next());
            }
        }

        // ✅ Verify salle status changed to Libre
        try (PreparedStatement ps = conn.prepareStatement(
                "SELECT status FROM salle WHERE id = ?")) {

            ps.setInt(1, salleId);
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    assertEquals("Libre", rs.getString("status"));
                }
            }
        }
    }
}
