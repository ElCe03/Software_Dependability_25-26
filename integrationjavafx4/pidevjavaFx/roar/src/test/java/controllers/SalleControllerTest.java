package controllers;

import entite.etage;
import entite.salle;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class SalleControllerTest {

    private SalleController controller;
    private etage etageTest;

    @BeforeEach
    void setUp() {
        controller = new SalleController();
        etageTest = new etage();
        etageTest.setId(1);
        etageTest.setNumero(1);
    }

    @Test
    void testBuildSalle_OK() {
        salle result = controller.buildSalleFromFields(
                "Salle 101", "20", "Consultation", "Disponible", 5, etageTest, "img.png");

        assertNotNull(result);
        assertEquals("Salle 101", result.getNom());
        assertEquals(20, result.getCapacite());
        assertEquals("Consultation", result.getType_salle());
    }

    @Test
    void testNomVide() {
        Exception exception = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildSalleFromFields("", "20", "Type", "Status", 1, etageTest, "");
        });
        assertEquals("Le nom est obligatoire", exception.getMessage());
    }

    @Test
    void testCapaciteInvalide() {
        // Test non-numero
        Exception ex1 = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildSalleFromFields("Nom", "abc", "Type", "Status", 1, etageTest, "");
        });
        assertEquals("Capacité invalide", ex1.getMessage());

        // Test numero negativo
        Exception ex2 = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildSalleFromFields("Nom", "-5", "Type", "Status", 1, etageTest, "");
        });
        assertEquals("La capacité doit être positive", ex2.getMessage());
    }

    @Test
    void testEtageNull() {
        Exception exception = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildSalleFromFields("Nom", "10", "Type", "Status", 1, null, "");
        });
        assertEquals("L'étage est obligatoire", exception.getMessage());
    }
}