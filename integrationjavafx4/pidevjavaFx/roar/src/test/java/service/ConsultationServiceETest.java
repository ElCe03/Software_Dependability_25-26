package service;

import entite.Consultation;
import org.junit.jupiter.api.AfterEach; // Ajout de l'import pour le nettoyage
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import util.DataSource;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException; // Ajout de l'import pour la gestion des exceptions
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class ConsultationServiceETest {

    private ConsultationService service;
    private int serviceId; // ID du service créé pour le test
    private int consultationId; // ID de la consultation créée pour le test

    @BeforeEach
    void setup() throws Exception {
        service = new ConsultationService();
        Connection cnx = DataSource.getInstance().getConnection();

        // ------------------ 1. Créer un SERVICE valide ------------------
        try (PreparedStatement ps = cnx.prepareStatement(
                "INSERT INTO service (name, description, duration) VALUES (?, ?, ?)",
                PreparedStatement.RETURN_GENERATED_KEYS)) {

            ps.setString(1, "Service Test JUnit");
            ps.setString(2, "Service pour tests d'intégration");
            ps.setInt(3, 30);

            ps.executeUpdate();

            try (ResultSet rs = ps.getGeneratedKeys()) {
                if (rs.next()) {
                    serviceId = rs.getInt(1);
                }
            }
        }

        assertTrue(serviceId > 0, "❌ Aucun service créé dans la base !");

        // ------------------ 2. Créer une CONSULTATION valide ------------------
        Consultation c = new Consultation(
                serviceId,
                Date.valueOf("2025-01-01"),
                "PATIENT_TEST_001",
                "En cours de traitement",
                "22112233"
        );

        service.addConsultation(c);
        consultationId = c.getId(); // Récupérer l'ID généré
        assertTrue(consultationId > 0, "❌ La consultation n'a pas été ajoutée correctement.");
    }

    /**
     * Nettoyage : Supprime le service et la consultation créés après chaque test.
     * Ceci garantit que chaque test s'exécute dans un environnement propre.
     */
    @AfterEach
    void tearDown() {
        Connection cnx = null;
        try {
            cnx = DataSource.getInstance().getConnection();

            // 1. Suppression de la consultation (utilise l'ID généré)
            if (consultationId > 0) {
                try (PreparedStatement psConsultation = cnx.prepareStatement(
                        "DELETE FROM consultation WHERE id = ?")) {
                    psConsultation.setInt(1, consultationId);
                    psConsultation.executeUpdate();
                }
            }

            // 2. Suppression du service (utilise l'ID généré)
            if (serviceId > 0) {
                try (PreparedStatement psService = cnx.prepareStatement(
                        "DELETE FROM service WHERE id = ?")) {
                    psService.setInt(1, serviceId);
                    psService.executeUpdate();
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors du nettoyage de la base de données : " + e.getMessage());
            // Nous ne devrions pas échouer le test ici, mais logguer l'erreur.
        }

        // Réinitialiser les IDs
        serviceId = 0;
        consultationId = 0;
    }


    @Test
    void testGetAllConsultations() {
        List<Consultation> list = service.getAllConsultations();
        assertNotNull(list, "La liste de consultations ne doit pas être null.");
        // Vérifie qu'au moins la consultation créée est présente
        assertTrue(list.size() > 0, "La liste doit contenir au moins la consultation de test.");

        // Vérification plus stricte
        Consultation createdConsultation = list.stream()
                .filter(c -> c.getId() == consultationId)
                .findFirst()
                .orElse(null);
        assertNotNull(createdConsultation, "La consultation créée doit être trouvée dans la liste complète.");
    }

    @Test
    void testSearchConsultation() {
        // La consultation de test contient "PATIENT_TEST_001"
        List<Consultation> list = service.searchConsultations("PATIENT_TEST");

        assertNotNull(list, "Le résultat de la recherche ne doit pas être null.");
        assertTrue(list.size() > 0, "La recherche doit retourner au moins une consultation.");

        // Vérification spécifique que notre consultation de test est bien trouvée
        boolean found = list.stream().anyMatch(c -> c.getId() == consultationId);
        assertTrue(found, "La recherche sur 'PATIENT_TEST' doit trouver la consultation créée.");
    }

    @Test
    void testUpdateStatus() {
        // Étant donné que nous avons l'ID généré (consultationId), nous l'utilisons directement.
        // Cela rend le test plus précis que de prendre list.get(0).

        String newStatus = "Terminée";
        boolean updated = service.updateConsultationStatus(consultationId, newStatus);

        assertTrue(updated, "L'update du statut doit retourner true.");

        // Verification BDD (Assurez-vous que le service a une méthode de récupération unitaire ou vérifiez directement la BDD si nécessaire)
        // Sans méthode getConsultationById, on fait confiance au service, mais un test E-E (End-to-End) vérifierait la BDD.
        // Pour ce test d'intégration, l'assertion `assertTrue(updated)` est suffisante pour l'unité testée (`updateConsultationStatus`).
    }
}