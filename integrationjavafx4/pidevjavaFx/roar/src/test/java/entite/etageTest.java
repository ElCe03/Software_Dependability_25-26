package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
class etageTest {

    @Mock
    private entite.departement departementMock;

    @Test
    void testDefaultConstructor() {
        etage e = new etage();

        assertEquals(0, e.getId());
        assertEquals(0, e.getNumero());
        assertEquals(0, e.getNbrSalle());
        assertNull(e.getDepartement());
    }

    @Test
    void testParameterizedConstructor() {
        int id = 10;
        int numero = 2;

        etage e = new etage(id, numero, departementMock);

        assertEquals(id, e.getId());
        assertEquals(numero, e.getNumero());
        assertEquals(departementMock, e.getDepartement());
        assertEquals(0, e.getNbrSalle());
    }

    @Test
    void testSettersAndGetters() {
        etage e = new etage();

        e.setId(5);
        e.setNumero(3);
        e.setNbrSalle(15);
        e.setDepartement(departementMock);

        assertEquals(5, e.getId());
        assertEquals(3, e.getNumero());
        assertEquals(15, e.getNbrSalle());
        assertEquals(departementMock, e.getDepartement());
    }

    @Test
    void testNbrSalleIndependence() {
        etage e = new etage(1, 1, departementMock);
        
        assertEquals(0, e.getNbrSalle());
        
        e.setNbrSalle(10);
        assertEquals(10, e.getNbrSalle());
    }

    @Test
    void testDepartementRelationshipUpdate() {
        etage e = new etage();
        assertNull(e.getDepartement());

        e.setDepartement(departementMock);
        assertNotNull(e.getDepartement());
        assertEquals(departementMock, e.getDepartement());

        e.setDepartement(null);
        assertNull(e.getDepartement());
    }
}