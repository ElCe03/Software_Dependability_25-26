package controllers;

import entite.Entretien;
import entite.Equipement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
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
        equipement.setNom("Scanner");
    }

    // ✅ TEST 1 — Création d'un entretien valide
    @Test
    void testBuildEntretien_OK() throws Exception {
        Method method = AjouterEntretienController.class
                .getDeclaredMethod("buildEntretienFromFields",
                        Equipement.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Entretien entretien = (Entretien) method.invoke(
                controller,
                equipement,
                "Maintenance annuelle",
                LocalDate.now().plusDays(2)
        );

        assertNotNull(entretien);
        assertEquals("Scanner", entretien.getNomEquipement());
        assertEquals("Maintenance annuelle", entretien.getDescription());
        assertEquals(1, entretien.getEquipementId());
    }

    // ✅ TEST 2 — Description vide déclenche exception
    @Test
    void testDescriptionVide() throws Exception {
        Method method = AjouterEntretienController.class
                .getDeclaredMethod("buildEntretienFromFields",
                        Equipement.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        equipement,
                        "",
                        LocalDate.now().plusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 3 — Date nulle déclenche exception
    @Test
    void testDateNull() throws Exception {
        Method method = AjouterEntretienController.class
                .getDeclaredMethod("buildEntretienFromFields",
                        Equipement.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        equipement,
                        "Test",
                        null)
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 4 — Date passée déclenche exception
    @Test
    void testDatePassee() throws Exception {
        Method method = AjouterEntretienController.class
                .getDeclaredMethod("buildEntretienFromFields",
                        Equipement.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        equipement,
                        "Test entretien",
                        LocalDate.now().minusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Date invalide", ex.getCause().getMessage());
    }

    // ✅ TEST 5 — Equipement null déclenche exception
    @Test
    void testEquipementNull() throws Exception {
        Method method = AjouterEntretienController.class
                .getDeclaredMethod("buildEntretienFromFields",
                        Equipement.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        null,
                        "Test",
                        LocalDate.now().plusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }
}
