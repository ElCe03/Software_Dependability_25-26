package service;

import entite.Equipement;
import org.junit.jupiter.api.*;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
public class EquipementServiceETest {

    private static EquipementService equipementService;
    private static int equipementId;

    @BeforeAll
    static void setup() {
        equipementService = new EquipementService();
        System.out.println("✅ Setup terminé");
    }

    @Test
    @Order(1)
    void testAjouterEquipement() {
        Equipement e = new Equipement(
                0,
                "Test Equipement",
                "Medical",
                "Disponible",
                "TestCategory"
        );

        equipementService.ajouterEquipement(e);

        List<Equipement> list = equipementService.getAllEquipements();
        assertFalse(list.isEmpty(), "❌ La liste d'équipements ne doit pas être vide");

        Equipement last = list.get(list.size() - 1);
        equipementId = last.getId();

        assertEquals("Test Equipement", last.getNom());
        System.out.println("✅ Ajout testé avec succès");
    }

    @Test
    @Order(2)
    void testGetEquipementById() {
        Equipement e = equipementService.getEquipementById(equipementId);

        assertNotNull(e, "❌ L'équipement ne doit pas être null");
        assertEquals("Test Equipement", e.getNom());
        System.out.println("✅ Get by ID testé");
    }

    @Test
    @Order(3)
    void testUpdateEquipement() {
        Equipement e = equipementService.getEquipementById(equipementId);

        e.setNom("Equipement Modifié");
        e.setStatut("En panne");

        equipementService.updateEquipement(e);

        Equipement updated = equipementService.getEquipementById(equipementId);

        assertEquals("Equipement Modifié", updated.getNom());
        assertEquals("En panne", updated.getStatut());

        System.out.println("✅ Update testé");
    }

    @Test
    @Order(4)
    void testGetEquipementsByCategory() {
        List<Equipement> list = equipementService.getEquipementsByCategory("TestCategory");
        assertFalse(list.isEmpty());
        System.out.println("✅ Recherche par catégorie testée");
    }

    @Test
    @Order(5)
    void testSupprimerEquipement() {
        equipementService.supprimerEquipement(equipementId);

        Equipement e = equipementService.getEquipementById(equipementId);
        assertNull(e);

        System.out.println("✅ Suppression testée");
    }
}
