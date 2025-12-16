package service;

import entite.Entretien;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class EntretienServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private EntretienService entretienService;

    @BeforeEach
    public void setup() throws SQLException {
        entretienService.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.createStatement()).thenReturn(mockStatement);
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.executeUpdate()).thenReturn(1); // Simule 1 ligne affectée par défaut
    }

    @Test
    public void testAjouterEntretien() throws SQLException {
        Entretien e = new Entretien(0, 1, LocalDate.now(), "Test entretien", "Equip Test", LocalDateTime.now());
        
        entretienService.ajouterEntretien(e);

       verify(mockConnection).prepareStatement(contains("INSERT INTO entretien"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    public void testGetAllEntretiens() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, true, false);
        
        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getInt("equipement_id")).thenReturn(10);
        when(mockResultSet.getDate("date")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getString("description")).thenReturn("Maintenance A", "Maintenance B");
        when(mockResultSet.getString("nom_equipement")).thenReturn("Scanner");
        when(mockResultSet.getTimestamp("created_at")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));

        List<Entretien> entretiens = entretienService.getAllEntretiens();
        
        assertNotNull(entretiens);
        assertEquals(2, entretiens.size());
        assertEquals("Maintenance A", entretiens.get(0).getDescription());
    }

    @Test
    public void testUpdateEntretien() throws SQLException {
        Entretien e = new Entretien(1, 1, LocalDate.now(), "Update Desc", "Scanner", LocalDateTime.now());

        entretienService.updateEntretien(e);

        verify(mockConnection).prepareStatement(contains("UPDATE entretien"));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    public void testDeleteEntretien() throws SQLException {
        int idToDelete = 5;
        
        entretienService.deleteEntretien(idToDelete);

        verify(mockConnection).prepareStatement(contains("DELETE FROM entretien"));
        verify(mockPreparedStatement).setInt(1, idToDelete);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    public void testGetEntretienById() throws SQLException {
        int idToFind = 10;

        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(idToFind);
        when(mockResultSet.getInt("equipement_id")).thenReturn(5);
        when(mockResultSet.getDate("date")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getString("description")).thenReturn("Description Trouvée");
        when(mockResultSet.getString("nom_equipement")).thenReturn("Equipement X");
        when(mockResultSet.getTimestamp("created_at")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));

        Entretien result = entretienService.getEntretienById(idToFind);

        assertNotNull(result);
        assertEquals(idToFind, result.getId());
        assertEquals("Description Trouvée", result.getDescription());
    }
}