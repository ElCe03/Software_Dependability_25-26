package service;

import entite.Consultation;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import util.DataSource;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class ConsultationServiceETest {

    private ConsultationService service;
    private int serviceId;

    @BeforeEach
    void setup() throws Exception {
        service = new ConsultationService();
        Connection cnx = DataSource.getInstance().getConnection();

        // ✅ 1. Créer un SERVICE valide avec duration
        try (PreparedStatement ps = cnx.prepareStatement(
                "INSERT INTO service (name, description, duration) VALUES (?, ?, ?)",
                PreparedStatement.RETURN_GENERATED_KEYS)) {

            ps.setString(1, "Service Test");
            ps.setString(2, "Service pour tests JUnit");
            ps.setInt(3, 30); // ✅ DURATION OBLIGATOIRE

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    serviceId = rs.getInt(1);
                }
            }
        }

        assertTrue(serviceId > 0, "❌ Aucun service créé dans la base !");

        // ✅ 2. Créer une CONSULTATION valide
        Consultation c = new Consultation(
                serviceId,
                Date.valueOf("2025-01-01"),
                "PATIENT_TEST_001",
                "En cours de traitement",
                "22112233"
        );

        service.addConsultation(c);
        assertTrue(c.getId() > 0);
    }

    @Test
    void testGetAllConsultations() {
        List<Consultation> list = service.getAllConsultations();
        assertNotNull(list);
        assertTrue(list.size() > 0);
    }

    @Test
    void testSearchConsultation() {
        List<Consultation> list = service.searchConsultations("PATIENT_TEST");
        assertNotNull(list);
        assertTrue(list.size() > 0);
    }

    @Test
    void testUpdateStatus() {
        List<Consultation> list = service.getAllConsultations();
        assertFalse(list.isEmpty());

        Consultation c = list.get(0);
        boolean updated = service.updateConsultationStatus(c.getId(), "Terminée");

        assertTrue(updated);
    }
}
