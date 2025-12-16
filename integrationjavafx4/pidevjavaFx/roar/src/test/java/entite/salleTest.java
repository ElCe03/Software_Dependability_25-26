package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
class salleTest {

    @Mock
    private etage etageMock;

    @Test
    void testDefaultConstructor() {
        salle s = new salle();

        assertEquals(0, s.getId());
        assertEquals(0, s.getCapacite());
        assertEquals(0, s.getPriorite());
        assertNull(s.getNom());
        assertNull(s.getType_salle());
        assertNull(s.getStatus());
        assertNull(s.getEtage());
        assertNull(s.getImage());
    }

    @Test
    void testConstructorWithIdNameCapaciteStatus() {
        int id = 101;
        String nom = "Salle A";
        int capacite = 50;
        String status = "Open";

        salle s = new salle(id, nom, capacite, status);

        assertEquals(id, s.getId());
        assertEquals(nom, s.getNom());
        assertEquals(capacite, s.getCapacite());
        assertEquals(status, s.getStatus());
        assertEquals(0, s.getPriorite());
        assertNull(s.getImage());
    }

    @Test
    void testConstructorWithIdNameStatus() {
        int id = 102;
        String nom = "Salle B";
        String status = "Closed";

        salle s = new salle(id, nom, status);

        assertEquals(id, s.getId());
        assertEquals(nom, s.getNom());
        assertEquals(status, s.getStatus());
        assertEquals(0, s.getCapacite()); 
    }

    @Test
    void testFullDetailsConstructor() {
        String nom = "Salle VIP";
        int capacite = 10;
        String type = "Meeting";
        String image = "vip.png";
        String status = "Reserved";
        int priorite = 5;

        salle s = new salle(nom, capacite, type, image, status, priorite);

        assertEquals(0, s.getId());
        assertEquals(nom, s.getNom());
        assertEquals(capacite, s.getCapacite());
        assertEquals(type, s.getType_salle());
        assertEquals(image, s.getImage());
        assertEquals(status, s.getStatus());
        assertEquals(priorite, s.getPriorite());
    }

    @Test
    void testSettersAndGetters() {
        salle s = new salle();

        s.setId(99);
        s.setNom("Conference Hall");
        s.setCapacite(200);
        s.setType_salle("Conference");
        s.setStatus("Cleaning");
        s.setImage("hall.jpg");
        s.setPriorite(1);

        assertEquals(99, s.getId());
        assertEquals("Conference Hall", s.getNom());
        assertEquals(200, s.getCapacite());
        assertEquals("Conference", s.getType_salle());
        assertEquals("Cleaning", s.getStatus());
        assertEquals("hall.jpg", s.getImage());
        assertEquals(1, s.getPriorite());
    }

    @Test
    void testEtageRelationship() {
        salle s = new salle();
        
        assertNull(s.getEtage());

        s.setEtage(etageMock);
        
        assertNotNull(s.getEtage());
        assertEquals(etageMock, s.getEtage());
    }
}