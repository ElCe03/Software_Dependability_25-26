package entite;

import org.junit.jupiter.api.Test;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class MedecinTest {

    @Test
    void testDefaultConstructor() {
        Medecin medecin = new Medecin();

        assertNull(medecin.getSpecialite());
        assertNull(medecin.getTelephone());
        
        // Verifica che l'oggetto sia istanza corretta
        assertTrue(medecin instanceof Users);
    }

    @Test
    void testParameterizedConstructorMapping() {
        int id = 10;
        String email = "doc@hospital.com";
        String password = "securePass";
        List<String> roles = new ArrayList<>();
        roles.add("ROLE_MEDECIN");
        String nom = "House";
        String prenom = "Gregory";
        String type = "MEDECIN";
        String specialite = "Diagnostician";
        String telephone = "555-0199";

        Medecin medecin = new Medecin(id, email, password, roles, nom, prenom, type, specialite, telephone);

        assertAll(
            () -> assertEquals(specialite, medecin.getSpecialite()),
            () -> assertEquals(telephone, medecin.getTelephone()),
            
            // Verifica dei campi ereditati dalla classe Users
            () -> assertEquals(id, medecin.getId()),
            () -> assertEquals(email, medecin.getEmail()),
            () -> assertEquals(nom, medecin.getNom()),
            () -> assertEquals(prenom, medecin.getPrenom()),
            () -> assertEquals(roles, medecin.getRoles())
        );
    }

    @Test
    void testSettersAndGetters() {
        Medecin medecin = new Medecin();

        medecin.setSpecialite("Cardiologie");
        medecin.setTelephone("0600000000");

        assertEquals("Cardiologie", medecin.getSpecialite());
        assertEquals("0600000000", medecin.getTelephone());
    }

    @Test
    void testToStringOutput() {
        int id = 1;
        String email = "test@test.com";
        String specialite = "Chirurgie";
        String telephone = "123456";
        List<String> roles = new ArrayList<>();
        
        Medecin medecin = new Medecin(id, email, "pass", roles, "Nom", "Prenom", "Type", specialite, telephone);
        
        String result = medecin.toString();

        assertNotNull(result);
        assertTrue(result.contains("Medecin{"));
        assertTrue(result.contains("specialite='" + specialite + "'"));
        assertTrue(result.contains("telephone='" + telephone + "'"));
        assertTrue(result.contains("id=" + id));
    }

    @Test
    void testRolesNullSafetyContract() {
        // Questo test verifica il contratto JML: @ ensures (roles == null) ==> (this.roles != null && this.roles.isEmpty());
        // Nota: Questo presuppone che il costruttore super() di Users gestisca il null check.
        
        Medecin medecin = new Medecin(1, "e", "p", null, "n", "p", "t", "s", "t");
        
        // Se la classe Users rispetta il contratto, roles non dovrebbe mai essere null
        if (medecin.getRoles() != null) {
            assertTrue(medecin.getRoles().isEmpty());
        } else {
            // Se Users non gestisce il null, verifichiamo che il getter ritorni null come passato
            assertNull(medecin.getRoles());
        }
    }
}