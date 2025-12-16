package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.Timestamp;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
class reservationTest {

    @Mock
    private salle salleMock;

    @Test
    void testDefaultConstructor() {
        reservation r = new reservation();

        assertEquals(0, r.getId());
        assertNull(r.getSalle());
        assertNull(r.getDate_debut());
        assertNull(r.getDate_fin());
    }

    @Test
    void testParameterizedConstructor() {
        int id = 10;
        Timestamp debut = Timestamp.valueOf("2023-10-01 10:00:00");
        Timestamp fin = Timestamp.valueOf("2023-10-01 12:00:00");

        reservation r = new reservation(id, salleMock, debut, fin);

        assertEquals(id, r.getId());
        assertEquals(salleMock, r.getSalle());
        assertEquals(debut, r.getDate_debut());
        assertEquals(fin, r.getDate_fin());
    }

    @Test
    void testSettersAndGetters() {
        reservation r = new reservation();
        
        int id = 50;
        Timestamp debut = Timestamp.valueOf("2024-01-01 08:30:00");
        Timestamp fin = Timestamp.valueOf("2024-01-01 18:30:00");

        r.setId(id);
        r.setSalle(salleMock);
        r.setDate_debut(debut);
        r.setDate_fin(fin);

        assertEquals(id, r.getId());
        assertEquals(salleMock, r.getSalle());
        assertEquals(debut, r.getDate_debut());
        assertEquals(fin, r.getDate_fin());
    }

    @Test
    void testTimestampIndependence() {
        Timestamp original = Timestamp.valueOf("2023-01-01 10:00:00");
        reservation r = new reservation();
        r.setDate_debut(original);

        assertEquals(original, r.getDate_debut());
        assertEquals(original.getTime(), r.getDate_debut().getTime());
    }

    @Test
    void testSalleAssociationUpdate() {
        reservation r = new reservation();
        r.setSalle(null);
        assertNull(r.getSalle());

        r.setSalle(salleMock);
        assertEquals(salleMock, r.getSalle());
    }
}