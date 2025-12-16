package service;

import entite.departement;
import entite.etage;
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
class EtageServiceTest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPstmt;
    @Mock
    private Statement mockStmt;
    @Mock
    private ResultSet mockRs;

    private EtageService etageService;

    @BeforeEach
    void setUp() {
        etageService = new EtageService(() -> mockConnection);
    }

    @Test
    void testAddEtage() throws SQLException {
        departement d = new departement();
        d.setId(5);
        etage e = new etage(0, 1, d);

        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPstmt);
        
        ResultSet mockKeys = mock(ResultSet.class);
        when(mockPstmt.getGeneratedKeys()).thenReturn(mockKeys);
        when(mockKeys.next()).thenReturn(true);
        when(mockKeys.getInt(1)).thenReturn(10); 

        etageService.addEtage(e);

        verify(mockPstmt).setInt(1, 1); 
        verify(mockPstmt).setInt(2, 5); 
        verify(mockPstmt).executeUpdate();
        assertEquals(10, e.getId());
    }

    @Test
    void testGetAllEtages() throws SQLException {
        when(mockConnection.createStatement()).thenReturn(mockStmt);
        when(mockStmt.executeQuery(anyString())).thenReturn(mockRs);

        when(mockRs.next()).thenReturn(true, false);
        
        when(mockRs.getInt("id")).thenReturn(1);
        when(mockRs.getInt("numero")).thenReturn(2);
        
        when(mockRs.getInt("departement_id")).thenReturn(10);
        when(mockRs.getString("departement_nom")).thenReturn("Cardiologie");
        when(mockRs.getString("adresse")).thenReturn("Batiment A");

        List<etage> result = etageService.getAllEtages();

        assertEquals(1, result.size());
        assertEquals(2, result.get(0).getNumero());
        assertEquals("Cardiologie", result.get(0).getDepartement().getNom());
    }

    @Test
    void testUpdateEtage() throws SQLException {
        departement d = new departement();
        d.setId(5);
        etage e = new etage(1, 3, d);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);

        etageService.updateEtage(e);

        verify(mockPstmt).setInt(1, 3); 
        verify(mockPstmt).setInt(2, 5); 
        verify(mockPstmt).setInt(3, 1); 
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testDeleteEtage() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);

        etageService.deleteEtage(1);

        verify(mockPstmt).setInt(1, 1);
        verify(mockPstmt).executeUpdate();
    }

    @Test
    void testSearchEtages() throws SQLException {
        String term = "Cardio";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true, false);

        when(mockRs.getInt("id")).thenReturn(1);
        when(mockRs.getInt("numero")).thenReturn(2);
        when(mockRs.getInt("departement_id")).thenReturn(10);
        when(mockRs.getString("departement_nom")).thenReturn("Cardiologie");
        when(mockRs.getString("adresse")).thenReturn("Batiment A");

        List<etage> result = etageService.searchEtages(term);

        assertEquals(1, result.size());
        verify(mockPstmt, times(3)).setString(anyInt(), eq("%Cardio%"));
    }

    @Test
    void testGetEtagesByDepartement() throws SQLException {
        int depId = 5;
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true, false);

        when(mockRs.getInt("id")).thenReturn(100);
        when(mockRs.getInt("numero")).thenReturn(1);

        List<etage> result = etageService.getEtagesByDepartement(depId);

        assertEquals(1, result.size());
        assertEquals(1, result.get(0).getNumero());
        assertEquals(depId, result.get(0).getDepartement().getId());
        verify(mockPstmt).setInt(1, depId);
    }

    @Test
    void testGetEtageById() throws SQLException {
        int etageId = 10;
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);

        when(mockRs.getInt("id")).thenReturn(etageId);
        when(mockRs.getInt("numero")).thenReturn(2);
        when(mockRs.getInt("departement_id")).thenReturn(50);
        when(mockRs.getString("departement_nom")).thenReturn("Radio");
        when(mockRs.getString("adresse")).thenReturn("Bat C");

        etage result = etageService.getEtageById(etageId);

        assertNotNull(result);
        assertEquals(etageId, result.getId());
        assertEquals("Radio", result.getDepartement().getNom());
    }

    @Test
    void testCountEtagesByDepartement() throws SQLException {
        int depId = 7;
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);
        when(mockRs.getInt(1)).thenReturn(5);

        int count = etageService.countEtagesByDepartement(depId);

        assertEquals(5, count);
        verify(mockPstmt).setInt(1, depId);
    }
}