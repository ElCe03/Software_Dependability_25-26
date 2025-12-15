package service;

import entite.Commande;
import entite.Medicament;
import org.junit.jupiter.api.*;
import util.DataSource;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
@Tag("integration") // Integration test classification
class CommandeServiceETest {

    private CommandeService commandeService;
    private Connection cnx;
    private Commande testCommande;
    private Medicament testMedicament;

    @BeforeEach
    void setup() throws SQLException {
        cnx = DataSource.getInstance().getConnection();
        commandeService = new CommandeService();

        // ---------- Medicament ----------
        testMedicament = new Medicament();
        testMedicament.setNom_medicament("Paracetamol");
        testMedicament.setDescription_medicament("Test Medicament");
        testMedicament.setType_medicament("Comprime");
        testMedicament.setPrix_medicament(5.0);
        testMedicament.setQuantite_stock(100);
        testMedicament.setDate_entree(LocalDate.now());
        testMedicament.setDate_expiration(LocalDate.now().plusYears(1));

        try (PreparedStatement pst = cnx.prepareStatement(
                "INSERT INTO medicament (nom_medicament, description_medicament, type_medicament, prix_medicament, quantite_stock, date_entree, date_expiration) VALUES (?, ?, ?, ?, ?, ?, ?)",
                PreparedStatement.RETURN_GENERATED_KEYS)) {

            pst.setString(1, testMedicament.getNom_medicament());
            pst.setString(2, testMedicament.getDescription_medicament());
            pst.setString(3, testMedicament.getType_medicament());
            pst.setDouble(4, testMedicament.getPrix_medicament());
            pst.setInt(5, testMedicament.getQuantite_stock());
            pst.setDate(6, Date.valueOf(testMedicament.getDate_entree()));
            pst.setDate(7, Date.valueOf(testMedicament.getDate_expiration()));
            pst.executeUpdate();

            try (var rs = pst.getGeneratedKeys()) {
                if (rs.next()) testMedicament.setId(rs.getInt(1));
            }
        }

        // ---------- Commande ----------
        testCommande = new Commande();
        testCommande.setDate_commande(LocalDate.now());
        testCommande.setTotal_prix(50.0);
        testCommande.setQuantite(10);
        testCommande.setStripeSessionId("test_session");
        testCommande.setStatus("pending");
        testCommande.addMedicament(testMedicament, 5);
    }

    @AfterEach
    void cleanup() throws SQLException {
        if (cnx != null && !cnx.isClosed()) {
            cnx.createStatement().executeUpdate("DELETE FROM medicament_commande");
            cnx.createStatement().executeUpdate("DELETE FROM commande");
            cnx.createStatement().executeUpdate("DELETE FROM medicament");
            cnx.close();
        }
    }

    // ---------------- CRUD TESTS ----------------
    @Test
    @Order(1)
    void testCreateCommande() {
        assertDoesNotThrow(() -> commandeService.create(testCommande));
        assertTrue(testCommande.getId() > 0);
    }

    @Test
    @Order(2)
    void testReadAllCommandes() {
        commandeService.create(testCommande);
        List<Commande> commandes = commandeService.readAll();
        assertFalse(commandes.isEmpty());
    }

    @Test
    @Order(3)
    void testReadById() {
        commandeService.create(testCommande);
        Commande c = commandeService.readById(testCommande.getId());
        assertNotNull(c);
        assertEquals(testCommande.getId(), c.getId());
    }

    @Test
    @Order(4)
    void testUpdateCommande() {
        commandeService.create(testCommande);
        testCommande.setStatus("completed");
        assertDoesNotThrow(() -> commandeService.update(testCommande));
        assertEquals("completed",
                commandeService.readById(testCommande.getId()).getStatus());
    }

    @Test
    @Order(5)
    void testDeleteCommande() {
        commandeService.create(testCommande);
        assertDoesNotThrow(() -> commandeService.delete(testCommande));
        assertNull(commandeService.readById(testCommande.getId()));
    }

    // ---------------- NEGATIVE / ROBUSTNESS TESTS ----------------
    @Test
    @Order(6)
    void testReadByInvalidId() {
        assertNull(commandeService.readById(-1));
    }

    @Test
    @Order(7)
    void testDeleteNonExistingCommande() {
        Commande fake = new Commande();
        fake.setId(-999);
        assertDoesNotThrow(() -> commandeService.delete(fake));
    }
}
