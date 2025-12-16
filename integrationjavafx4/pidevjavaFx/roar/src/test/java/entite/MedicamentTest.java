package entite;

import org.junit.jupiter.api.Test;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class MedicamentTest {

    @Test
    void testDefaultConstructor() {
        Medicament m = new Medicament();

        assertEquals(0, m.getId());
        assertEquals(0.0, m.getPrix_medicament());
        assertEquals(0, m.getQuantite_stock());
        assertNull(m.getNom_medicament());
        assertNull(m.getDate_entree());
        assertNull(m.getDate_expiration());
    }

    @Test
    void testFullConstructor() {
        int id = 100;
        String nom = "Paracetamolo";
        String desc = "Antipiretico";
        String type = "Analgesico";
        double prix = 5.50;
        int stock = 50;
        LocalDate entree = LocalDate.of(2023, 1, 1);
        LocalDate expiration = LocalDate.of(2025, 1, 1);

        Medicament m = new Medicament(id, nom, desc, type, prix, stock, entree, expiration);

        assertEquals(id, m.getId());
        assertEquals(nom, m.getNom_medicament());
        assertEquals(desc, m.getDescription_medicament());
        assertEquals(type, m.getType_medicament());
        assertEquals(prix, m.getPrix_medicament());
        assertEquals(stock, m.getQuantite_stock());
        assertEquals(entree, m.getDate_entree());
        assertEquals(expiration, m.getDate_expiration());
    }

    @Test
    void testConstructorWithoutId() {
        String nom = "Ibuprofene";
        String desc = "Anti-infiammatorio";
        String type = "FANS";
        double prix = 8.20;
        int stock = 20;
        LocalDate entree = LocalDate.now();
        LocalDate expiration = entree.plusYears(2);

        Medicament m = new Medicament(nom, desc, type, prix, stock, entree, expiration);

        assertEquals(0, m.getId());
        assertEquals(nom, m.getNom_medicament());
        assertEquals(prix, m.getPrix_medicament());
        assertEquals(expiration, m.getDate_expiration());
    }

    @Test
    void testSettersAndGetters() {
        Medicament m = new Medicament();

        m.setId(5);
        m.setNom_medicament("Aspirina");
        m.setDescription_medicament("Mal di testa");
        m.setType_medicament("Composse");
        m.setPrix_medicament(12.50);
        m.setQuantite_stock(100);
        LocalDate date = LocalDate.of(2024, 5, 10);
        m.setDate_entree(date);
        m.setDate_expiration(date.plusDays(30));

        assertEquals(5, m.getId());
        assertEquals("Aspirina", m.getNom_medicament());
        assertEquals("Mal di testa", m.getDescription_medicament());
        assertEquals("Composse", m.getType_medicament());
        assertEquals(12.50, m.getPrix_medicament());
        assertEquals(100, m.getQuantite_stock());
        assertEquals(date, m.getDate_entree());
        assertNotNull(m.getDate_expiration());
    }

    @Test
    void testDateLogicValidBoundary() {
        Medicament m = new Medicament();
        LocalDate today = LocalDate.now();
        
        m.setDate_entree(today);
        m.setDate_expiration(today); 
        
        assertEquals(m.getDate_entree(), m.getDate_expiration());
    }

    @Test
    void testToStringReturnsNameOnly() {
        Medicament m = new Medicament();
        String expectedName = "TestDrug";
        m.setNom_medicament(expectedName);
        
        assertEquals(expectedName, m.toString());
    }
}