package service;

import entite.Medicament;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class MedicamentServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private MedicamentService service;

    @BeforeEach
    void setup() throws Exception {
        service.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.createStatement()).thenReturn(mockStatement);
        
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.executeUpdate()).thenReturn(1);
    }

    @Test
    void testCreate() throws SQLException {
        Medicament m = new Medicament();
        m.setNom_medicament("Doliprane Test");
        m.setDescription_medicament("Test description");
        m.setType_medicament("Antalgique");
        m.setPrix_medicament(5.5);
        m.setQuantite_stock(100);
        m.setDate_entree(LocalDate.now());
        m.setDate_expiration(LocalDate.now().plusDays(20));

        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(55);

        service.create(m);

        verify(mockConnection).prepareStatement(contains("INSERT INTO"), eq(Statement.RETURN_GENERATED_KEYS));
        verify(mockPreparedStatement).executeUpdate();
        assertEquals(55, m.getId());
    }

    @Test
    void testReadById() throws SQLException {
        when(mockResultSet.next()).thenReturn(true);
        
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("nom_medicament")).thenReturn("Doliprane Test");
        when(mockResultSet.getString("description_medicament")).thenReturn("Description Test"); // AGGIUNTO
        when(mockResultSet.getString("type_medicament")).thenReturn("Antalgique");
        when(mockResultSet.getDouble("prix_medicament")).thenReturn(5.5); // AGGIUNTO
        when(mockResultSet.getInt("quantite_stock")).thenReturn(100); // AGGIUNTO
        when(mockResultSet.getDate("date_entree")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getDate("date_expiration")).thenReturn(Date.valueOf(LocalDate.now()));

        Medicament m = service.readById(1);

        assertNotNull(m);
        assertEquals("Doliprane Test", m.getNom_medicament());
        assertEquals("Description Test", m.getDescription_medicament());
        assertEquals("Antalgique", m.getType_medicament());
    }

    @Test
    void testReadAll() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, false); // 1 record, poi fine
        
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("nom_medicament")).thenReturn("Doliprane Test");
        when(mockResultSet.getString("description_medicament")).thenReturn("Desc");
        when(mockResultSet.getString("type_medicament")).thenReturn("TypeA");
        when(mockResultSet.getDouble("prix_medicament")).thenReturn(10.0);
        when(mockResultSet.getInt("quantite_stock")).thenReturn(50);
        when(mockResultSet.getDate("date_entree")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getDate("date_expiration")).thenReturn(Date.valueOf(LocalDate.now()));

        List<Medicament> list = service.readAll();

        assertNotNull(list);
        assertEquals(1, list.size());
        assertEquals("Doliprane Test", list.get(0).getNom_medicament());
    }

    @Test
    void testUpdate() throws SQLException {
        Medicament m = new Medicament();
        m.setId(1);
        m.setPrix_medicament(9.9);
        m.setQuantite_stock(50);
        m.setDate_entree(LocalDate.now());
        m.setDate_expiration(LocalDate.now());

        service.update(m);

        verify(mockConnection).prepareStatement(contains("UPDATE medicament"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDelete() throws SQLException {
        Medicament m = new Medicament();
        m.setId(1);

        service.delete(m);

        verify(mockConnection).prepareStatement(contains("DELETE FROM medicament"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testGetTypeCounts() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString("type_medicament")).thenReturn("Antalgique");
        when(mockResultSet.getInt("count")).thenReturn(10);

        Map<String, Integer> result = service.getTypeCounts();

        assertNotNull(result);
        assertEquals(1, result.size());
        assertTrue(result.containsKey("Antalgique"));
        assertEquals(10, result.get("Antalgique"));
    }

    @Test
    void testGetMedicamentsProchesExpiration() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, false);
        
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("nom_medicament")).thenReturn("Expiring Med");
        when(mockResultSet.getString("description_medicament")).thenReturn("Desc");
        when(mockResultSet.getString("type_medicament")).thenReturn("TypeB");
        when(mockResultSet.getDouble("prix_medicament")).thenReturn(12.0);
        when(mockResultSet.getInt("quantite_stock")).thenReturn(20);
        when(mockResultSet.getDate("date_entree")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getDate("date_expiration")).thenReturn(Date.valueOf(LocalDate.now().plusDays(5)));

        List<Medicament> list = service.getMedicamentsProchesExpiration();

        assertNotNull(list);
        assertEquals(1, list.size());
    }
}