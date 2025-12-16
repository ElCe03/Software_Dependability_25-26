package entite;

import org.junit.jupiter.api.Test;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class UsersTest {

    @Test
    void testDefaultConstructor() {
        Users user = new Users();

        assertEquals(0, user.getId());
        assertNotNull(user.getRoles());
        assertTrue(user.getRoles().isEmpty());
        assertNull(user.getEmail());
        assertNull(user.getPassword());
        assertNull(user.getNom());
        assertNull(user.getPrenom());
        assertNull(user.getType());
    }

    @Test
    void testParameterizedConstructorFull() {
        int id = 1;
        String email = "admin@test.com";
        String password = "hashedpass";
        List<String> roles = new ArrayList<>(Arrays.asList("ADMIN", "USER"));
        String nom = "Admin";
        String prenom = "Super";
        String type = "INTERNAL";

        Users user = new Users(id, email, password, roles, nom, prenom, type);

        assertEquals(id, user.getId());
        assertEquals(email, user.getEmail());
        assertEquals(password, user.getPassword());
        assertEquals(roles, user.getRoles());
        assertEquals(nom, user.getNom());
        assertEquals(prenom, user.getPrenom());
        assertEquals(type, user.getType());
    }

    @Test
    void testParameterizedConstructorNullRolesSafety() {
        Users user = new Users(1, "test@test.com", "pass", null, "Nom", "Prenom", "Type");

        assertNotNull(user.getRoles());
        assertTrue(user.getRoles().isEmpty());
    }

    @Test
    void testWeirdSignatureConstructor() {
        Users user = new Users(10, "Dupont", "Jean", "mail@test.com", "ROLE", "Medecin");

        assertEquals(0, user.getId());
        assertNull(user.getNom());
        assertNull(user.getPrenom());
        assertNull(user.getEmail());
        
        assertNotNull(user.getRoles());
        assertTrue(user.getRoles().isEmpty());
    }

    @Test
    void testSettersAndGetters() {
        Users user = new Users();

        user.setId(55);
        user.setEmail("user@domain.com");
        user.setPassword("secret");
        user.setNom("Rossi");
        user.setPrenom("Mario");
        user.setType("PATIENT");

        List<String> newRoles = new ArrayList<>();
        newRoles.add("GUEST");
        user.setRoles(newRoles);

        assertEquals(55, user.getId());
        assertEquals("user@domain.com", user.getEmail());
        assertEquals("secret", user.getPassword());
        assertEquals("Rossi", user.getNom());
        assertEquals("Mario", user.getPrenom());
        assertEquals("PATIENT", user.getType());
        assertEquals(newRoles, user.getRoles());
    }

    @Test
    void testToString() {
        Users user = new Users(1, "a@b.c", "pwd", null, "N", "P", "T");
        String result = user.toString();

        assertNotNull(result);
        assertTrue(result.contains("id=1"));
        assertTrue(result.contains("email='a@b.c'"));
        assertTrue(result.contains("nom='N'"));
        assertTrue(result.contains("prenom='P'"));
        assertTrue(result.contains("roles=[]"));
    }
}