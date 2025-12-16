package entite;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class departementTest {

    @Test
    void testDefaultConstructor() {
        departement dep = new departement();

        assertEquals(0, dep.getId());
        assertEquals(0, dep.getNbr_etage());
        assertNull(dep.getNom());
        assertNull(dep.getAdresse());
        assertNull(dep.getImage());
    }

    @Test
    void testThreeArgumentConstructor() {
        String nom = "RH";
        String adresse = "Batiment A";
        String image = "logo.png";

        departement dep = new departement(nom, adresse, image);

        assertEquals(0, dep.getId());
        assertEquals(nom, dep.getNom());
        assertEquals(adresse, dep.getAdresse());
        assertEquals(image, dep.getImage());
        assertEquals(0, dep.getNbr_etage());
    }

    @Test
    void testFullConstructor() {
        int id = 10;
        String nom = "IT";
        String adresse = "Batiment C";
        String image = "tech.png";

        departement dep = new departement(id, nom, adresse, image);

        assertEquals(id, dep.getId());
        assertEquals(nom, dep.getNom());
        assertEquals(adresse, dep.getAdresse());
        assertEquals(image, dep.getImage());
        assertEquals(0, dep.getNbr_etage());
    }

    @Test
    void testSettersAndGetters() {
        departement dep = new departement();

        dep.setId(99);
        dep.setNom("Marketing");
        dep.setAdresse("Rue de la Paix");
        dep.setImage("mkt.jpg");
        dep.setNbr_etage(5);

        assertEquals(99, dep.getId());
        assertEquals("Marketing", dep.getNom());
        assertEquals("Rue de la Paix", dep.getAdresse());
        assertEquals("mkt.jpg", dep.getImage());
        assertEquals(5, dep.getNbr_etage());
    }

    @Test
    void testSetNbrEtageTypoMethod() {
        departement dep = new departement();
        dep.setNbr_etage(2); 

        dep.setNbr_Etage(10); 

        assertEquals(2, dep.getNbr_etage());
    }

    @Test
    void testToStringReturnsNull() {
        departement dep = new departement(1, "Test", "Addr", "Img");
        assertNull(dep.toString());
    }
    
    @Test
    void testSetNbrEtageFunctional() {
        departement dep = new departement();
        dep.setNbr_etage(10);
        assertEquals(10, dep.getNbr_etage());
    }
}