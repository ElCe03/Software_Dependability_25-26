package controllers;

import entite.Entretien;
import entite.Equipement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import java.time.LocalDate;
import static org.junit.jupiter.api.Assertions.*;

class AjouterEntretienControllerTest {

    private AjouterEntretienController controller;
    private Equipement equipement;

    @BeforeEach
    void setUp() {
        controller = new AjouterEntretienController();
        equipement = new Equipement();
        equipement.setId(1);
        equipement.setNom("IRM");
    }

    @Test
    void testBuildEntretien_OK() {
        // Passiamo 'equipement' (tipo Equipement) al metodo
        Entretien result = controller.buildEntretienFromFields(
                equipement, "Maintenance préventive", LocalDate.now().plusDays(1));

        assertNotNull(result);
        assertEquals("IRM", result.getNomEquipement());
        assertEquals("Maintenance préventive", result.getDescription());
    }

    @Test
    void testEquipementNull() {
        // Passiamo null dove si aspetta Equipement
        Exception ex = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildEntretienFromFields(null, "Desc", LocalDate.now());
        });
        assertEquals("Aucun équipement défini !", ex.getMessage());
    }

    @Test
    void testDescriptionVide() {
        Exception ex = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildEntretienFromFields(equipement, "", LocalDate.now());
        });
        assertEquals("La description est obligatoire", ex.getMessage());
    }

    @Test
    void testDateNull() {
        Exception ex = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildEntretienFromFields(equipement, "Desc", null);
        });
        assertEquals("La date est obligatoire", ex.getMessage());
    }

    @Test
    void testDatePassee() {
        Exception ex = assertThrows(IllegalArgumentException.class, () -> {
            controller.buildEntretienFromFields(equipement, "Desc", LocalDate.now().minusDays(1));
        });
        assertEquals("La date ne peut pas être dans le passé", ex.getMessage());
    }
}