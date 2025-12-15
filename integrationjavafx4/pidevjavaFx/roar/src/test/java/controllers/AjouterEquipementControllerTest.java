package controllers;

import entite.Equipement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.*;

class AjouterEquipementControllerTest {

    private AjouterEquipementController controller;

    @BeforeEach
    void setUp() {
        controller = new AjouterEquipementController();
    }

    // ✅ TEST 1 — Création OK
    @Test
    void testBuildEquipement_OK() throws Exception {
        Method method = AjouterEquipementController.class
                .getDeclaredMethod("buildEquipementFromFields",
                        String.class, String.class, String.class, String.class);
        method.setAccessible(true);

        Equipement e = (Equipement) method.invoke(
                controller,
                "Scanner",
                "Médical",
                "Disponible",
                "Radiologie"
        );

        assertEquals("Scanner", e.getNom());
        assertEquals("Médical", e.getType());
        assertEquals("Disponible", e.getStatut());
        assertEquals("Radiologie", e.getCategory());
    }

    // ✅ TEST 2 — Nom vide
    @Test
    void testNomVide() throws Exception {
        Method method = AjouterEquipementController.class
                .getDeclaredMethod("buildEquipementFromFields",
                        String.class, String.class, String.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "",
                        "Type",
                        "Disponible",
                        "Cat")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 3 — Statut null
    @Test
    void testStatutNull() throws Exception {
        Method method = AjouterEquipementController.class
                .getDeclaredMethod("buildEquipementFromFields",
                        String.class, String.class, String.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Echo",
                        "Médical",
                        null,
                        "Imagerie")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
    }

    // ✅ TEST 4 — Catégorie vide
    @Test
    void testCategorieVide() throws Exception {
        Method method = AjouterEquipementController.class
                .getDeclaredMethod("buildEquipementFromFields",
                        String.class, String.class, String.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "IRM",
                        "Imagerie",
                        "Disponible",
                        "")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
    }
}
