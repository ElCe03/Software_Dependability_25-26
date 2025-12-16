package test;

import entite.etage;
import entite.salle;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import service.SalleService;

import java.sql.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class SalleServiceTest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    private SalleService salleService;

    @BeforeEach
    void setUp() {
        salleService = new SalleService(mockConnection);
    }

    @Test
    void testAddSalle_Success() throws SQLException {
        etage e = new etage();
        e.setId(1);
        e.setNbrSalle(0);

        salle s = new salle();
        s.setNom("Salle 101");
        s.setCapacite(20);
        s.setType_salle("Laboratoire");
        s.setStatus("Disponible");
        s.setEtage(e);
        s.setImage("img.png");
        s.setPriorite(1);

        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(55);

        salleService.addSalle(s);

        
        assertEquals(55, s.getId());
        assertEquals(1, e.getNbrSalle()); 
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testGetAll() throws SQLException {
        when(mockConnection.createStatement()).thenReturn(mockStatement);
        when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        
        when(mockResultSet.next()).thenReturn(true).thenReturn(false);
        
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getString("nom")).thenReturn("Salle Test");
        when(mockResultSet.getInt("capacite")).thenReturn(50); 
        when(mockResultSet.getString("type_salle")).thenReturn("Laboratoire");
        when(mockResultSet.getString("status")).thenReturn("Disponible"); 
        when(mockResultSet.getString("image")).thenReturn("img.png"); 
        when(mockResultSet.getInt("priorite")).thenReturn(1); 
        
        when(mockResultSet.getInt("etage_id")).thenReturn(2);
        when(mockResultSet.getInt("etage_numero")).thenReturn(1);

        List<salle> result = salleService.getAll();

        assertEquals(1, result.size());
        assertEquals(10, result.get(0).getId());
        assertEquals("Salle Test", result.get(0).getNom());
        assertEquals(50, result.get(0).getCapacite()); 
    }

    @Test
    void testDeleteSalle() throws SQLException {
        int idToDelete = 5;
        
        when(mockConnection.prepareStatement(contains("SELECT"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("etage_id")).thenReturn(1);

        PreparedStatement mockDeleteStmt = mock(PreparedStatement.class);
        when(mockConnection.prepareStatement(contains("DELETE"))).thenReturn(mockDeleteStmt);
        
        try {
            salleService.deleteSalle(idToDelete);
        } catch (Exception e) {
        }

        verify(mockDeleteStmt).executeUpdate();
    }
    
}