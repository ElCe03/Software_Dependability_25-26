package service;

import entite.Commande;
import entite.Medicament;
import entite.MedicamentCommande;
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
class CommandeServiceETest {

    private CommandeService commandeService;
    private Connection cnx;
    private Commande testCommande;
    private Medicament testMedicament;

    @BeforeEach
    void setup() throws SQLException {
        // Crée une connexion isolée pour chaque test
        cnx = DataSource.getInstance().getConnection();
        commandeService = new CommandeService();

        // Créer un médicament de test
        testMedicament = new Medicament();
        testMedicament.setNom_medicament("Paracetamol");
        testMedicament.setDescription_medicament("Test Médicament");
        testMedicament.setType_medicament("Comprimé");
        testMedicament.setPrix_medicament(5.0);
        testMedicament.setQuantite_stock(100);
        testMedicament.setDate_entree(LocalDate.now());
        testMedicament.setDate_expiration(LocalDate.now().plusYears(1));

        // Insertion directe du médicament dans la base pour test
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

        // Créer une commande de test
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
        // Supprime la commande et le médicament directement pour ne rien laisser
        if (cnx != null && !cnx.isClosed()) {
            cnx.createStatement().executeUpdate("DELETE FROM medicament_commande");
            cnx.createStatement().executeUpdate("DELETE FROM commande");
            cnx.createStatement().executeUpdate("DELETE FROM medicament");
            cnx.close();
        }
    }

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
        Commande c = commandeService.readById(testCommande.getId());
        assertEquals("completed", c.getStatus());
    }

    @Test
    @Order(5)
    void testDeleteCommande() {
        commandeService.create(testCommande);
        assertDoesNotThrow(() -> commandeService.delete(testCommande));
        Commande c = commandeService.readById(testCommande.getId());
        assertNull(c);
    }
}
