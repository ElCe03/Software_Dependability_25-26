package entite;

import org.junit.jupiter.api.Test;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class StaffTest {

    @Test
    void testDefaultConstructor() {
        Staff staff = new Staff();

        assertNull(staff.getTelephone());
        assertTrue(staff instanceof Users);
    }

    @Test
    void testParameterizedConstructorMapping() {
        int id = 30;
        String email = "staff@admin.com";
        String password = "admin";
        List<String> roles = new ArrayList<>();
        roles.add("ROLE_STAFF");
        String type = "STAFF";
        String nom = "Wayne";
        String prenom = "Bruce";
        String telephone = "555-12345";

        Staff staff = new Staff(id, email, password, roles, type, nom, prenom, telephone);

        assertAll(
            () -> assertEquals(id, staff.getId()),
            () -> assertEquals(email, staff.getEmail()),
            () -> assertEquals(nom, staff.getNom()),
            () -> assertEquals(prenom, staff.getPrenom()),
            () -> assertEquals(roles, staff.getRoles()),
            () -> assertEquals(telephone, staff.getTelephone())
        );
    }

    @Test
    void testSettersAndGetters() {
        Staff staff = new Staff();
        String phone = "000-111-222";

        staff.setTelephone(phone);

        assertEquals(phone, staff.getTelephone());
    }

    @Test
    void testToStringOutput() {
        Staff staff = new Staff();
        staff.setId(99);
        staff.setNom("Kent");
        staff.setTelephone("999-888");

        String result = staff.toString();

        assertNotNull(result);
        assertTrue(result.contains("Staff{"));
        assertTrue(result.contains("id=99"));
        assertTrue(result.contains("nom='Kent'"));
        assertTrue(result.contains("telephone='999-888'"));
    }

    @Test
    void testNullableFields() {
        Staff staff = new Staff(1, "e", "p", null, "t", "n", "p", null);

        assertNull(staff.getTelephone());
        
        if (staff.getRoles() != null) {
            assertTrue(staff.getRoles().isEmpty());
        }
    }
}