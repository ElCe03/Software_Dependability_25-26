package controllers;

import entite.Entretien;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

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
    void testBuildUpdatedEntretien_OK() {
        // On appelle la méthode directement car elle est publique
        Entretien updated = controller.buildUpdatedEntretien(
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
    void testNomVide() {
        Exception ex = assertThrows(IllegalArgumentException.class, () ->
                controller.buildUpdatedEntretien(
                        entretien,
                        "",
                        "Description",
                        LocalDate.now().plusDays(1))
        );

        // On vérifie le message exact défini dans le contrôleur
        assertEquals("Le nom est obligatoire", ex.getMessage());
    }

    // ✅ TEST 3 — Description vide
    @Test
    void testDescriptionVide() {
        Exception ex = assertThrows(IllegalArgumentException.class, () ->
                controller.buildUpdatedEntretien(
                        entretien,
                        "Scanner",
                        "",
                        LocalDate.now().plusDays(1))
        );

        assertEquals("La description est obligatoire", ex.getMessage());
    }

    // ✅ TEST 4 — Date nulle
    @Test
    void testDateNull() {
        Exception ex = assertThrows(IllegalArgumentException.class, () ->
                controller.buildUpdatedEntretien(
                        entretien,
                        "Scanner",
                        "Test",
                        null)
        );

        assertEquals("La date est obligatoire", ex.getMessage());
    }

    // ✅ TEST 5 — Date dans le passé
    @Test
    void testDatePassee() {
        Exception ex = assertThrows(IllegalArgumentException.class, () ->
                controller.buildUpdatedEntretien(
                        entretien,
                        "Scanner",
                        "Test",
                        LocalDate.now().minusDays(1))
        );

        assertEquals("La date ne peut pas être dans le passé", ex.getMessage());
    }

    // ✅ TEST 6 — Entretien null
    @Test
    void testEntretienNull() {
        Exception ex = assertThrows(IllegalArgumentException.class, () ->
                controller.buildUpdatedEntretien(
                        null,
                        "Test",
                        "Desc",
                        LocalDate.now().plusDays(1))
        );

        assertEquals("L'entretien à modifier est null", ex.getMessage());
    }
}