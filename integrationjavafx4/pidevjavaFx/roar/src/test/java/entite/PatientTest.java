package entite;

import org.junit.jupiter.api.Test;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class PatientTest {

    @Test
    void testDefaultConstructor() {
        Patient patient = new Patient();

        assertNull(patient.getAdresse());
        assertNull(patient.getTelephone());
        assertNull(patient.getDateNaissance());
        assertTrue(patient instanceof Users);
    }

    @Test
    void testParameterizedConstructorMapping() {
        int id = 5;
        String email = "patient@test.com";
        String password = "secret";
        List<String> roles = new ArrayList<>();
        roles.add("PATIENT");
        String type = "PATIENT";
        String nom = "Rossi";
        String prenom = "Mario";
        String adresse = "Via Roma 1";
        String telephone = "123456789";
        LocalDate dob = LocalDate.of(1990, 1, 1);

        Patient patient = new Patient(id, email, password, roles, type, nom, prenom, adresse, telephone, dob);

        assertAll(
            () -> assertEquals(id, patient.getId()),
            () -> assertEquals(email, patient.getEmail()),
            () -> assertEquals(nom, patient.getNom()),
            () -> assertEquals(prenom, patient.getPrenom()),
            () -> assertEquals(roles, patient.getRoles()),
            () -> assertEquals(adresse, patient.getAdresse()),
            () -> assertEquals(telephone, patient.getTelephone()),
            () -> assertEquals(dob, patient.getDateNaissance())
        );
    }

    @Test
    void testSettersAndGetters() {
        Patient patient = new Patient();

        String addr = "Corso Italia 10";
        String phone = "987654321";
        LocalDate dob = LocalDate.of(1985, 12, 25);

        patient.setAdresse(addr);
        patient.setTelephone(phone);
        patient.setDateNaissance(dob);

        assertEquals(addr, patient.getAdresse());
        assertEquals(phone, patient.getTelephone());
        assertEquals(dob, patient.getDateNaissance());
    }

    @Test
    void testToStringOutput() {
        Patient patient = new Patient();
        patient.setId(1);
        patient.setNom("Bianchi");
        patient.setAdresse("Milano");
        patient.setDateNaissance(LocalDate.of(2000, 1, 1));

        String result = patient.toString();

        assertNotNull(result);
        assertTrue(result.contains("Patient{"));
        assertTrue(result.contains("adresse='Milano'"));
        assertTrue(result.contains("nom='Bianchi'"));
        assertTrue(result.contains("dateNaissance=2000-01-01"));
    }

    @Test
    void testNullableFields() {
        Patient patient = new Patient(1, "e", "p", null, "t", "n", "p", null, null, null);

        assertNull(patient.getAdresse());
        assertNull(patient.getTelephone());
        assertNull(patient.getDateNaissance());
    }
}