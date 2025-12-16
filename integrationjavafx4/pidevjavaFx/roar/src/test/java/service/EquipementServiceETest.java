package service;

import entite.Equipement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class EquipementServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private EquipementService equipementService;

    @BeforeEach
    void setup() throws SQLException {
        equipementService.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.createStatement()).thenReturn(mockStatement);
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.executeUpdate()).thenReturn(1);
    }

    @Test
    void testAjouterEquipement() throws SQLException {
        Equipement e = new Equipement(0, "Test Equipement", "Medical", "Disponible", "TestCategory");

        equipementService.ajouterEquipement(e);

        verify(mockConnection).prepareStatement(contains("INSERT INTO equipement"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testGetEquipementById() throws SQLException {
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("nom")).thenReturn("Test Equipement");
        when(mockResultSet.getString("type")).thenReturn("Medical");
        when(mockResultSet.getString("statut")).thenReturn("Disponible");
        when(mockResultSet.getString("category")).thenReturn("TestCategory");

        Equipement e = equipementService.getEquipementById(1);

        assertNotNull(e, "❌ L'équipement ne doit pas être null");
        assertEquals("Test Equipement", e.getNom());
    }

    @Test
    void testUpdateEquipement() throws SQLException {
        Equipement e = new Equipement(1, "Equipement Modifié", "Type", "En panne", "Cat");

        equipementService.updateEquipement(e);

        verify(mockConnection).prepareStatement(contains("UPDATE equipement"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testGetEquipementsByCategory() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, true, false); // 2 items
        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getString("nom")).thenReturn("Eq1", "Eq2");

        List<Equipement> list = equipementService.getEquipementsByCategory("TestCategory");
        
        assertFalse(list.isEmpty());
        assertEquals(2, list.size());
    }

    @Test
    void testSupprimerEquipement() throws SQLException {
        equipementService.supprimerEquipement(1);

        verify(mockConnection).prepareStatement(contains("DELETE FROM equipement"));
        verify(mockPreparedStatement).executeUpdate();
    }
}