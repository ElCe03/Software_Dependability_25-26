package service;

import entite.departement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class DepartemntServiceTest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPstmt;
    @Mock
    private ResultSet mockRs;

    private DepartemntService departementService;

    @BeforeEach
    void setUp() {
        
        departementService = new DepartemntService(() -> mockConnection);
    }

    @Test
    void testAddDepartement() throws SQLException {
        
        departement dep = new departement(0, "Cardiologia", "Piano 1", "img.jpg");

        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPstmt);
        
        ResultSet mockGeneratedKeys = mock(ResultSet.class);
        when(mockPstmt.getGeneratedKeys()).thenReturn(mockGeneratedKeys);
        when(mockGeneratedKeys.next()).thenReturn(true);
        when(mockGeneratedKeys.getInt(1)).thenReturn(15); 

        departementService.addDepartement(dep);

        assertEquals(15, dep.getId(), "L'ID dovrebbe essere aggiornato dopo l'inserimento");
        verify(mockPstmt).setString(1, "Cardiologia");
        verify(mockPstmt).setString(2, "Piano 1");
        verify(mockPstmt).setString(3, "img.jpg");
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testGetAllDepartements() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);

        when(mockRs.next()).thenReturn(true, true, false);
        
        when(mockRs.getInt("id")).thenReturn(1, 2);
        when(mockRs.getString("nom")).thenReturn("Cardio", "Neuro");
        when(mockRs.getString("adresse")).thenReturn("A1", "B2");
        when(mockRs.getString("image")).thenReturn("img1.png", "img2.png");
        when(mockRs.getInt("etage_count")).thenReturn(3, 0);

        List<departement> result = departementService.getAllDepartements();

        assertEquals(2, result.size());
        assertEquals("Cardio", result.get(0).getNom());
        assertEquals(3, result.get(0).getNbr_etage());
        assertEquals("Neuro", result.get(1).getNom());
        assertEquals(0, result.get(1).getNbr_etage());
    }

    @Test
    void testUpdateDepartement() throws SQLException {
        departement dep = new departement(10, "Updated", "New Addr", "new.jpg");
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);

        departementService.updateDepartement(dep);

        verify(mockPstmt).setString(1, "Updated");
        verify(mockPstmt).setInt(4, 10); 
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testDeleteDepartement_ById() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        departementService.deleteDepartement(5);

        verify(mockPstmt).setInt(1, 5);
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testDeleteDepartement_ByObject() throws SQLException {
        departement dep = new departement();
        dep.setId(8);
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);

        departementService.deleteDepartement(dep);

        verify(mockPstmt).setInt(1, 8);
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testGetDepartementById_Found() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);

        when(mockRs.getInt("id")).thenReturn(99);
        when(mockRs.getString("nom")).thenReturn("Urgence");
        when(mockRs.getInt("etage_count")).thenReturn(5);

        departement result = departementService.getDepartementById(99);

        assertNotNull(result);
        assertEquals("Urgence", result.getNom());
        assertEquals(5, result.getNbr_etage());
        verify(mockPstmt).setInt(1, 99);
    }

    @Test
    void testGetDepartementById_NotFound() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(false); 
        departement result = departementService.getDepartementById(99);

        assertNull(result);
    }

    @Test
    void testSearchDepartements() throws SQLException {
        String term = "Radio";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        
        when(mockRs.next()).thenReturn(true, false); 
        when(mockRs.getString("nom")).thenReturn("Radiologie");

        List<departement> results = departementService.searchDepartements(term);

        assertEquals(1, results.size());
        assertEquals("Radiologie", results.get(0).getNom());
        
        verify(mockPstmt, times(3)).setString(anyInt(), eq("%Radio%"));
    }

    @Test
    void testExceptionHandling() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        assertThrows(RuntimeException.class, () -> {
            departementService.getAllDepartements();
        });
    }
}