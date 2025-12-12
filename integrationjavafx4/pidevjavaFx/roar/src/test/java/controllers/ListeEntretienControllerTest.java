package controllers;

import entite.Entretien;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import java.time.LocalDate;
import static org.junit.jupiter.api.Assertions.*;

class ListeEntretienControllerTest {

    private ListeEntretienController controller;

    @BeforeEach
    void setUp() {
        controller = new ListeEntretienController();
    }

    @Test
    void testBuildHtmlContent_OK() {
        Entretien e = new Entretien();
        e.setId(1);
        e.setNomEquipement("Scanner");
        e.setDate(LocalDate.now());
        e.setDescription("Test Description");

        String html = controller.buildHtmlContent(e);
        assertNotNull(html);
        assertTrue(html.contains("Scanner"));
        assertTrue(html.contains("Test Description"));
    }

    @Test
    void testBuildHtmlContent_DateNull() {
        Entretien e = new Entretien();
        e.setId(1);
        e.setNomEquipement("Scanner");
        e.setDate(null); // Data nulla
        e.setDescription("Desc");

        String html = controller.buildHtmlContent(e);
        
        // Verifica che contenga il valore di default che abbiamo messo nel controller
        assertTrue(html.contains("Non définie")); 
    }

    @Test
    void testBuildHtmlContent_NullEntretien() {
        // Verifica che lanci l'eccezione come da noi programmato
        assertThrows(RuntimeException.class, () -> {
            controller.buildHtmlContent(null);
        });
    }
}