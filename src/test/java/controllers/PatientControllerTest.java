
package controllers;

import entite.Patient;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.time.LocalDate;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.web.servlet.AutoConfigureMockMvc;
import org.springframework.test.web.servlet.MockMvc;

import static org.junit.jupiter.api.Assertions.*;
@AutoConfigureMockMvc
class PatientControllerTest {
    @Autowired
    private MockMvc mockMvc;

    private PatientController controller;

    @BeforeEach
    void setUp() {
        controller = new PatientController();
    }

    // ✅ TEST 1 — Données valides
    @Test
    void testBuildPatient_OK() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Patient patient = (Patient) method.invoke(controller,
                "Tunis Centre",
                "0612345678",
                LocalDate.of(2000, 1, 1)
        );

        assertNotNull(patient);
        assertEquals("Tunis Centre", patient.getAdresse());
        assertEquals("0612345678", patient.getTelephone());
        assertEquals(LocalDate.of(2000, 1, 1), patient.getDateNaissance());
    }

    // ✅ TEST 2 — Adresse vide
    @Test
    void testAdresseVide() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "",
                        "0612345678",
                        LocalDate.of(2000, 1, 1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 3 — Téléphone vide
    @Test
    void testTelephoneVide() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Tunis Centre",
                        "",
                        LocalDate.of(2000, 1, 1))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 4 — Date nulle
    @Test
    void testDateNull() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Tunis Centre",
                        "0612345678",
                        null)
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Champs manquants", ex.getCause().getMessage());
    }

    // ✅ TEST 5 — Date future
    @Test
    void testDateFuture() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Tunis Centre",
                        "0612345678",
                        LocalDate.now().plusDays(5))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Date invalide", ex.getCause().getMessage());
    }

    // ✅ TEST 6 — Date trop ancienne
    @Test
    void testDateTropAncienne() throws Exception {
        Method method = PatientController.class
                .getDeclaredMethod("buildPatientFromFields", String.class, String.class, LocalDate.class);
        method.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () ->
                method.invoke(controller,
                        "Tunis Centre",
                        "0612345678",
                        LocalDate.now().minusYears(130))
        );

        assertTrue(ex.getCause() instanceof IllegalArgumentException);
        assertEquals("Date invalide", ex.getCause().getMessage());
    }
}
