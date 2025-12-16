package entite;

import org.junit.jupiter.api.Test;
import java.time.LocalDate;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.*;

class EntretienTest {

    @Test
    void testDefaultConstructor() {
        Entretien e = new Entretien();

        assertEquals(0, e.getId());
        assertEquals(0, e.getEquipementId());
        assertNull(e.getDate());
        assertNull(e.getDescription());
        assertNull(e.getNomEquipement());
        assertNull(e.getCreatedAt());
    }

    @Test
    void testFullConstructor() {
        int id = 1;
        int equipId = 100;
        LocalDate date = LocalDate.of(2023, 10, 15);
        String desc = "Maintenance préventive";
        String nom = "Scanner IRM";
        LocalDateTime created = LocalDateTime.of(2023, 10, 1, 12, 0);

        Entretien e = new Entretien(id, equipId, date, desc, nom, created);

        assertEquals(id, e.getId());
        assertEquals(equipId, e.getEquipementId());
        assertEquals(date, e.getDate());
        assertEquals(desc, e.getDescription());
        assertEquals(nom, e.getNomEquipement());
        assertEquals(created, e.getCreatedAt());
    }

    @Test
    void testConstructorWithoutId() {
        int equipId = 200;
        LocalDate date = LocalDate.now();
        String desc = "Réparation urgente";
        String nom = "Echographe";
        LocalDateTime created = LocalDateTime.now();

        Entretien e = new Entretien(equipId, date, desc, nom, created);

        assertEquals(0, e.getId());
        assertEquals(equipId, e.getEquipementId());
        assertEquals(date, e.getDate());
        assertEquals(desc, e.getDescription());
        assertEquals(nom, e.getNomEquipement());
        assertEquals(created, e.getCreatedAt());
    }

    @Test
    void testSettersAndGetters() {
        Entretien e = new Entretien();

        e.setId(50);
        e.setEquipementId(500);
        LocalDate newDate = LocalDate.of(2024, 1, 1);
        e.setDate(newDate);
        e.setDescription("Test Desc");
        e.setNomEquipement("Test Equip");
        LocalDateTime newTime = LocalDateTime.of(2024, 1, 1, 10, 30);
        e.setCreatedAt(newTime);

        assertEquals(50, e.getId());
        assertEquals(500, e.getEquipementId());
        assertEquals(newDate, e.getDate());
        assertEquals("Test Desc", e.getDescription());
        assertEquals("Test Equip", e.getNomEquipement());
        assertEquals(newTime, e.getCreatedAt());
    }

    @Test
    void testNullableFields() {
        Entretien e = new Entretien(1, 1, LocalDate.now(), "Desc", "Nom", LocalDateTime.now());

        e.setDate(null);
        e.setDescription(null);
        e.setNomEquipement(null);
        e.setCreatedAt(null);

        assertNull(e.getDate());
        assertNull(e.getDescription());
        assertNull(e.getNomEquipement());
        assertNull(e.getCreatedAt());
    }

    @Test
    void testToString() {
        Entretien e = new Entretien(10, 20, LocalDate.of(2023, 1, 1), "Check", "Motor", null);
        String result = e.toString();

        assertTrue(result.contains("id=10"));
        assertTrue(result.contains("equipementId=20"));
        assertTrue(result.contains("description='Check'"));
        assertTrue(result.contains("nomEquipement='Motor'"));
    }
}