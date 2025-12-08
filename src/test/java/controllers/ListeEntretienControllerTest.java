package controllers;

import entite.Entretien;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class ListeEntretienControllerTest {

    private ListeEntretienController controller;
    private Entretien entretien;

    @BeforeEach
    void setUp() {
        controller = new ListeEntretienController();

        entretien = new Entretien();
        entretien.setId(1);
        entretien.setNomEquipement("Scanner");
        entretien.setDate(LocalDate.of(2025, 3, 10));
        entretien.setDescription("Maintenance annuelle");
    }

    @Test
    void testBuildHtmlContent_OK() throws Exception {
        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        String html = (String) method.invoke(controller, entretien);

        assertNotNull(html);
        assertTrue(html.contains("Scanner"));
        assertTrue(html.contains("Maintenance annuelle"));
        assertTrue(html.contains("2025-03-10"));
    }

    @Test
    void testBuildHtmlContent_NullEntretien() throws Exception {
        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        Exception exception = assertThrows(Exception.class, () ->
                method.invoke(controller, new Object[]{null})
        );

        assertNotNull(exception.getCause());
        assertTrue(exception.getCause() instanceof NullPointerException);
    }

    @Test
    void testBuildHtmlContent_DescriptionVide() throws Exception {
        entretien.setDescription("");

        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        String html = (String) method.invoke(controller, entretien);
        assertTrue(html.contains("Description:")); // label présent
    }

    @Test
    void testBuildHtmlContent_NomEquipementVide() throws Exception {
        entretien.setNomEquipement("");

        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        String html = (String) method.invoke(controller, entretien);
        assertTrue(html.contains("Équipement:")); // label présent
    }

    @Test
    void testBuildHtmlContent_DateNull() throws Exception {
        entretien.setDate(null);

        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        String html = (String) method.invoke(controller, entretien);
        assertTrue(html.contains("Date: Non définie")); // vérifie que null est géré
    }

    @Test
    void testBuildHtmlContent_NomEtDescriptionNull() throws Exception {
        entretien.setNomEquipement(null);
        entretien.setDescription(null);

        Method method = ListeEntretienController.class.getDeclaredMethod("buildHtmlContent", Entretien.class);
        method.setAccessible(true);

        String html = (String) method.invoke(controller, entretien);
        assertTrue(html.contains("Équipement:"));
        assertTrue(html.contains("Description:"));
    }
}
