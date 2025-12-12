package service;

import entite.Entretien;
import entite.Equipement;
import org.junit.jupiter.api.*;
import util.DataSource;

import java.sql.Connection;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class EntretienServiceETest {

    private EntretienService entretienService;
    private EquipementService equipementService;
    private int testEquipementId;

    @BeforeAll
    public void setupAll() {
        entretienService = new EntretienService();
        equipementService = new EquipementService();

        // Créer un équipement de test
        Equipement e = new Equipement(0, "Equip Test", "Type A", "Fonctionnel", "Catégorie1");
        equipementService.ajouterEquipement(e);

        // Récupérer son ID
        List<Equipement> allEquipements = equipementService.getAllEquipements();
        testEquipementId = allEquipements.get(allEquipements.size() - 1).getId();
    }

    @AfterAll
    public void cleanupAll() {
        // Supprimer l’équipement de test et ses entretiens
        equipementService.deleteEquipementAndDependents(testEquipementId);
    }

    @Test
    public void testAjouterEntretien() {
        Entretien e = new Entretien(0, testEquipementId, LocalDate.now(), "Test entretien", "Equip Test", LocalDateTime.now());
        entretienService.ajouterEntretien(e);

        List<Entretien> entretiens = entretienService.getAllEntretiens();
        boolean found = entretiens.stream().anyMatch(entretien -> "Test entretien".equals(entretien.getDescription()));
        assertTrue(found, "L'entretien ajouté doit être présent dans la base");
    }

    @Test
    public void testUpdateEntretien() {
        Entretien e = new Entretien(0, testEquipementId, LocalDate.now(), "Entretien à mettre à jour", "Equip Test", LocalDateTime.now());
        entretienService.ajouterEntretien(e);

        // Récupérer l’entretien ajouté
        Entretien toUpdate = entretienService.getAllEntretiens().get(entretienService.getAllEntretiens().size() - 1);
        toUpdate.setDescription("Entretien mis à jour");

        entretienService.updateEntretien(toUpdate);

        Entretien updated = entretienService.getEntretienById(toUpdate.getId());
        assertEquals("Entretien mis à jour", updated.getDescription());
    }

    @Test
    public void testDeleteEntretien() {
        Entretien e = new Entretien(0, testEquipementId, LocalDate.now(), "Entretien à supprimer", "Equip Test", LocalDateTime.now());
        entretienService.ajouterEntretien(e);

        Entretien toDelete = entretienService.getAllEntretiens().get(entretienService.getAllEntretiens().size() - 1);
        entretienService.deleteEntretien(toDelete.getId());

        Entretien deleted = entretienService.getEntretienById(toDelete.getId());
        assertNull(deleted, "L'entretien doit être supprimé et ne plus exister");
    }

    @Test
    public void testGetEntretienById() {
        Entretien e = new Entretien(0, testEquipementId, LocalDate.now(), "Test entretien", "Equip Test", LocalDateTime.now());
        entretienService.ajouterEntretien(e);

        Entretien retrieved = entretienService.getAllEntretiens().get(entretienService.getAllEntretiens().size() - 1);
        Entretien byId = entretienService.getEntretienById(retrieved.getId());

        assertNotNull(byId);
        assertEquals("Test entretien", byId.getDescription());
        assertEquals(testEquipementId, byId.getEquipementId());
    }
}
