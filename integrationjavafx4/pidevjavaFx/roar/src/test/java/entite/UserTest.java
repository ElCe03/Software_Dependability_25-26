package entite;

import org.junit.jupiter.api.Test;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class UserTest {

    @Test
    void testDefaultConstructor() {
        User user = new User();

        assertEquals(0, user.getId());
        assertNotNull(user.getRoles());
        assertTrue(user.getRoles().isEmpty());
        assertNull(user.getEmail());
    }

    @Test
    void testParameterizedConstructorFull() {
        String email = "test@user.com";
        String password = "pass";
        List<String> roles = new ArrayList<>(Arrays.asList("ROLE_USER"));
        String nom = "Doe";
        String prenom = "John";
        String type = "generic";
        String specialite = "N/A";
        String telephone = "123";
        String adresse = "City";
        LocalDate dob = LocalDate.of(1990, 1, 1);

        User user = new User(email, password, roles, nom, prenom, type, specialite, telephone, adresse, dob);

        assertAll(
            () -> assertEquals(email, user.getEmail()),
            () -> assertEquals(password, user.getPassword()),
            () -> assertEquals(roles, user.getRoles()),
            () -> assertEquals(nom, user.getNom()),
            () -> assertEquals(prenom, user.getPrenom()),
            () -> assertEquals(type, user.getType()),
            () -> assertEquals(specialite, user.getSpecialite()),
            () -> assertEquals(telephone, user.getTelephone()),
            () -> assertEquals(adresse, user.getAdresse()),
            () -> assertEquals(dob, user.getDateNaissance())
        );
    }

    @Test
    void testParameterizedConstructorNullRolesProtection() {
        User user = new User("e", "p", null, "n", "p", "t", "s", "t", "a", null);

        assertNotNull(user.getRoles());
        assertTrue(user.getRoles().isEmpty());
    }

    @Test
    void testAddRole() {
        User user = new User();
        user.addRole("ROLE_ADMIN");

        assertEquals(1, user.getRoles().size());
        assertTrue(user.getRoles().contains("ROLE_ADMIN"));

        user.addRole("ROLE_USER");
        assertEquals(2, user.getRoles().size());
    }

    @Test
    void testAddRoleLazyInitialization() {
        User user = new User();
        user.setRoles(null); 
        
        user.addRole("ROLE_NEW");
        
        assertNotNull(user.getRoles());
        assertEquals(1, user.getRoles().size());
        assertEquals("ROLE_NEW", user.getRoles().get(0));
    }

    @Test
    void testIsPatientByType() {
        User user = new User();
        
        user.setType("patient");
        assertTrue(user.isPatient());

        user.setType("PATIENT");
        assertTrue(user.isPatient());
    }

    @Test
    void testIsPatientByRole() {
        User user = new User();
        user.setType("unknown");
        
        assertFalse(user.isPatient());

        user.addRole("ROLE_PATIENT");
        assertTrue(user.isPatient());
    }

    @Test
    void testIsMedecinByType() {
        User user = new User();
        
        user.setType("medecin");
        assertTrue(user.isMedecin());

        user.setType("MEDECIN");
        assertTrue(user.isMedecin());

        user.setType("medcin");
        assertTrue(user.isMedecin());
    }

    @Test
    void testIsMedecinByRole() {
        User user = new User();
        user.setType("unknown");
        
        assertFalse(user.isMedecin());

        user.addRole("ROLE_MEDECIN");
        assertTrue(user.isMedecin());
        
        user.setRoles(new ArrayList<>());
        user.addRole("ROLE_MEDCIN");
        assertTrue(user.isMedecin());
    }

    @Test
    void testSettersAndGetters() {
        User user = new User();
        user.setId(100);
        user.setEmail("new@mail.com");
        user.setPassword("newpass");
        user.setNom("Smith");
        user.setPrenom("Jane");
        user.setType("Guest");
        user.setSpecialite("None");
        user.setTelephone("999");
        user.setAdresse("Street");
        user.setDateNaissance(LocalDate.now());

        assertEquals(100, user.getId());
        assertEquals("new@mail.com", user.getEmail());
        assertEquals("newpass", user.getPassword());
        assertEquals("Smith", user.getNom());
        assertEquals("Jane", user.getPrenom());
        assertEquals("Guest", user.getType());
        assertEquals("None", user.getSpecialite());
        assertEquals("999", user.getTelephone());
        assertEquals("Street", user.getAdresse());
        assertNotNull(user.getDateNaissance());
    }

    @Test
    void testToString() {
        User user = new User();
        user.setPrenom("Mario");
        user.setNom("Rossi");

        assertEquals("Mario Rossi", user.toString());
    }
}