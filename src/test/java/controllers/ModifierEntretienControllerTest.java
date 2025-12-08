package controllers;

import entite.Entretien;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class ModifierEntretienControllerTest {

    private ModifierEntretienController controller;
    private Entretien entretien;

    @BeforeEach
    void setUp() {
        controller = new ModifierEntretienController();

        entretien = new Entretien();
        entretien.setId(1);
        entretien.setNomEquipement("Scanner");
        entretien.setDescription("Ancienne description");
        entretien.setDate(LocalDate.now().plusDays(5));
    }

    // ✅ TEST 1 — Mise à jour OK
    @Test
    void testBuildUpdatedEntretien_OK() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Entretien updated = (Entretien) method.invoke(
                controller,
                entretien,
                "IRM",
                "Nouvelle description",
                LocalDate.now().plusDays(3)
        );

        assertEquals("IRM", updated.getNomEquipement());
        assertEquals("Nouvelle description", updated.getDescription());
        assertEquals(LocalDate.now().plusDays(3), updated.getDate());
    }

    // ✅ TEST 2 — Nom vide
    @Test
    void testNomVide() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        entretien,
                        "",
                        "Description",
                        LocalDate.now().plusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 3 — Description vide
    @Test
    void testDescriptionVide() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        entretien,
                        "Scanner",
                        "",
                        LocalDate.now().plusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 4 — Date nulle
    @Test
    void testDateNull() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        entretien,
                        "Scanner",
                        "Test",
                        null)
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 5 — Date dans le passé
    @Test
    void testDatePassee() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        entretien,
                        "Scanner",
                        "Test",
                        LocalDate.now().minusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Date invalide", ex.getCause().getMessage());
    }

    // ✅ TEST 6 — Entretien null
    @Test
    void testEntretienNull() throws Exception {

        Method method = ModifierEntretienController.class
                .getDeclaredMethod("buildUpdatedEntretien",
                        Entretien.class, String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        null,
                        "Test",
                        "Desc",
                        LocalDate.now().plusDays(1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }
}
