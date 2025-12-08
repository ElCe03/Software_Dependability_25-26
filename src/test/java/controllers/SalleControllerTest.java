package controllers;

import entite.etage;
import entite.salle;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.*;

class SalleControllerTest {

    private SalleController controller;
    private etage e;

    @BeforeEach
    void setUp() {
        controller = new SalleController();
        e = new etage();
        e.setId(1);
        e.setNumero(2);
    }

    // ✅ TEST 1 — Données valides
    @Test
    void testBuildSalle_OK() throws Exception {
        Method method = SalleController.class.getDeclaredMethod(
                "buildSalleFromFields", String.class, String.class, String.class,
                String.class, int.class, etage.class, String.class);
        method.setAccessible(true);

        salle s = (salle) method.invoke(controller,
                "Salle A",
                "10",
                "Consultation",
                "Disponible",
                1,
                e,
                "image.png"
        );

        assertNotNull(s);
        assertEquals("Salle A", s.getNom());
        assertEquals(10, s.getCapacite());
        assertEquals("Consultation", s.getType_salle());
        assertEquals("Disponible", s.getStatus());
        assertEquals(1, s.getPriorite());
        assertEquals(e, s.getEtage());
        assertEquals("image.png", s.getImage());
    }

    // ✅ TEST 2 — Nom vide
    @Test
    void testNomVide() throws Exception {
        Method method = SalleController.class.getDeclaredMethod(
                "buildSalleFromFields", String.class, String.class, String.class,
                String.class, int.class, etage.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "",
                        "10",
                        "Consultation",
                        "Disponible",
                        1,
                        e,
                        "image.png")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 3 — Capacité invalide
    @Test
    void testCapaciteInvalide() throws Exception {
        Method method = SalleController.class.getDeclaredMethod(
                "buildSalleFromFields", String.class, String.class, String.class,
                String.class, int.class, etage.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Salle B",
                        "abc",
                        "Consultation",
                        "Disponible",
                        1,
                        e,
                        "image.png")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Capacité invalide", ex.getCause().getMessage());
    }

    // ✅ TEST 4 — Etage null
    @Test
    void testEtageNull() throws Exception {
        Method method = SalleController.class.getDeclaredMethod(
                "buildSalleFromFields", String.class, String.class, String.class,
                String.class, int.class, etage.class, String.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Salle C",
                        "5",
                        "Consultation",
                        "Disponible",
                        1,
                        null,
                        "image.png")
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }
}
