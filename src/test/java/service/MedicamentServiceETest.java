package service;

import entite.Medicament;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import util.DataSource;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

public class MedicamentServiceETest {

    private MedicamentService service;
    private int medicamentId;

    @BeforeEach
    void setup() throws Exception {
        service = new MedicamentService();
        Connection cnx = DataSource.getInstance().getConnection();

        // ✅ 1. Insertion directe dans la BD
        try (PreparedStatement ps = cnx.prepareStatement(
                "INSERT INTO medicament (nom_medicament, description_medicament, type_medicament, prix_medicament, quantite_stock, date_entree, date_expiration) " +
                        "VALUES (?, ?, ?, ?, ?, ?, ?)",
                PreparedStatement.RETURN_GENERATED_KEYS)) {

            ps.setString(1, "Doliprane Test");
            ps.setString(2, "Test description");
            ps.setString(3, "Antalgique");
            ps.setDouble(4, 5.5);
            ps.setInt(5, 100);
            ps.setDate(6, Date.valueOf(LocalDate.now()));
            ps.setDate(7, Date.valueOf(LocalDate.now().plusDays(20))); // proche expiration ✅

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    medicamentId = rs.getInt(1);
                }
            }
        }

        assertTrue(medicamentId > 0, "❌ Aucun médicament créé !");
    }

    @Test
    void testCreateAndReadById() {
        Medicament m = service.readById(medicamentId);

        assertNotNull(m);
        assertEquals("Doliprane Test", m.getNom_medicament());
        assertEquals("Antalgique", m.getType_medicament());
    }

    @Test
    void testReadAll() {
        List<Medicament> list = service.readAll();

        assertNotNull(list);
        assertTrue(list.size() > 0);
    }

    @Test
    void testUpdate() {
        Medicament m = service.readById(medicamentId);
        assertNotNull(m);

        m.setPrix_medicament(9.9);
        m.setQuantite_stock(50);

        service.update(m);

        Medicament updated = service.readById(medicamentId);
        assertEquals(9.9, updated.getPrix_medicament());
        assertEquals(50, updated.getQuantite_stock());
    }

    @Test
    void testDelete() {
        Medicament m = service.readById(medicamentId);
        assertNotNull(m);

        service.delete(m);

        Medicament deleted = service.readById(medicamentId);
        assertNull(deleted);
    }

    @Test
    void testGetTypeCounts() {
        Map<String, Integer> result = service.getTypeCounts();

        assertNotNull(result);
        assertTrue(result.size() > 0);
        assertTrue(result.containsKey("Antalgique"));
    }

    @Test
    void testGetMedicamentsProchesExpiration() {
        List<Medicament> list = service.getMedicamentsProchesExpiration();

        assertNotNull(list);
        assertTrue(list.size() > 0);
    }
}
