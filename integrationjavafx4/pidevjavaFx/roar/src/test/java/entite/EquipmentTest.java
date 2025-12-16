package entite;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class EquipementTest {

    @Test
    void testDefaultConstructor() {
        Equipement eq = new Equipement();

        assertEquals(0, eq.getId());
        assertNull(eq.getNom());
        assertNull(eq.getType());
        assertNull(eq.getStatut());
        assertNull(eq.getCategory());
    }

    @Test
    void testFullConstructor() {
        int id = 10;
        String nom = "Scanner 3D";
        String type = "Imagerie";
        String statut = "Actif";
        String category = "Radiologie";

        Equipement eq = new Equipement(id, nom, type, statut, category);

        assertEquals(id, eq.getId());
        assertEquals(nom, eq.getNom());
        assertEquals(type, eq.getType());
        assertEquals(statut, eq.getStatut());
        assertEquals(category, eq.getCategory());
    }

    @Test
    void testPartialConstructor() {
        String nom = "Microscope";
        String type = "Laboratoire";
        String statut = "Maintenance";
        String category = "Biologie";

        Equipement eq = new Equipement(nom, type, statut, category);

        assertEquals(0, eq.getId());
        assertEquals(nom, eq.getNom());
        assertEquals(type, eq.getType());
        assertEquals(statut, eq.getStatut());
        assertEquals(category, eq.getCategory());
    }

    @Test
    void testSettersAndGetters() {
        Equipement eq = new Equipement();

        eq.setId(55);
        eq.setNom("Stéthoscope");
        eq.setType("Diagnostic");
        eq.setStatut("Disponible");
        eq.setCategory("Général");

        assertEquals(55, eq.getId());
        assertEquals("Stéthoscope", eq.getNom());
        assertEquals("Diagnostic", eq.getType());
        assertEquals("Disponible", eq.getStatut());
        assertEquals("Général", eq.getCategory());
    }

    @Test
    void testToString() {
        Equipement eq = new Equipement(1, "TestNom", "TestType", "TestStatut", "TestCat");
        String result = eq.toString();

        assertNotNull(result);
        assertTrue(result.contains("id=1"));
        assertTrue(result.contains("nom='TestNom'"));
        assertTrue(result.contains("type='TestType'"));
        assertTrue(result.contains("statut='TestStatut'"));
        assertTrue(result.contains("category='TestCat'"));
    }

    @Test
    void testNullableFields() {
        Equipement eq = new Equipement(1, "A", "B", "C", "D");
        
        eq.setNom(null);
        eq.setType(null);
        eq.setStatut(null);
        eq.setCategory(null);

        assertNull(eq.getNom());
        assertNull(eq.getType());
        assertNull(eq.getStatut());
        assertNull(eq.getCategory());
    }
}