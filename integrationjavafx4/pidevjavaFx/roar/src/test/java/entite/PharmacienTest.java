package entite;

import org.junit.jupiter.api.Test;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class PharmacienTest {

    @Test
    void testDefaultConstructor() {
        Pharmacien pharmacien = new Pharmacien();

        assertNull(pharmacien.getTelephone());
        assertTrue(pharmacien instanceof Users);
    }

    @Test
    void testParameterizedConstructorMapping() {
        int id = 20;
        String email = "pharma@med.com";
        String password = "secure";
        List<String> roles = new ArrayList<>();
        roles.add("ROLE_PHARMACIEN");
        String type = "PHARMACIEN";
        String nom = "Curie";
        String prenom = "Marie";
        String telephone = "0123456789";

        Pharmacien pharmacien = new Pharmacien(id, email, password, roles, type, nom, prenom, telephone);

        assertAll(
            () -> assertEquals(id, pharmacien.getId()),
            () -> assertEquals(email, pharmacien.getEmail()),
            () -> assertEquals(nom, pharmacien.getNom()),
            () -> assertEquals(prenom, pharmacien.getPrenom()),
            () -> assertEquals(roles, pharmacien.getRoles()),
            () -> assertEquals(telephone, pharmacien.getTelephone())
        );
    }

    @Test
    void testSettersAndGetters() {
        Pharmacien pharmacien = new Pharmacien();
        String newPhone = "0987654321";

        pharmacien.setTelephone(newPhone);

        assertEquals(newPhone, pharmacien.getTelephone());
    }

    @Test
    void testToStringOutput() {
        Pharmacien pharmacien = new Pharmacien();
        pharmacien.setId(5);
        pharmacien.setNom("Fleming");
        pharmacien.setTelephone("11223344");

        String result = pharmacien.toString();

        assertNotNull(result);
        assertTrue(result.contains("Pharmacien{"));
        assertTrue(result.contains("id=5"));
        assertTrue(result.contains("nom='Fleming'"));
        assertTrue(result.contains("telephone='11223344'"));
    }

    @Test
    void testNullableFields() {
        Pharmacien pharmacien = new Pharmacien(1, "e", "p", null, "t", "n", "p", null);

        assertNull(pharmacien.getTelephone());
        
        if (pharmacien.getRoles() != null) {
            assertTrue(pharmacien.getRoles().isEmpty());
        }
    }
}