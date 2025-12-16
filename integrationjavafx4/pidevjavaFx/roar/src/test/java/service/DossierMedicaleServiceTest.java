package service;

import entite.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class DossierMedicaleServiceTest {

    @Mock private Connection mockConnection;
    @Mock private PreparedStatement mockPstmt;
    @Mock private Statement mockStmt;
    @Mock private ResultSet mockRs;
    
    @Mock private UserService mockUserService; 
    @Mock private SejourService mockSejourService;

    private DossierMedicaleService dossierService;

    @BeforeEach
    void setUp() {
        dossierService = new DossierMedicaleService(() -> mockConnection, mockUserService);
        dossierService.setSejourService(mockSejourService);
    }

    @Test
    void testAjouterDossier() throws SQLException {
        User p = new User(); p.setId(1);
        User m = new User(); m.setId(2);
        
        DossierMedicale dossier = new DossierMedicale();
        dossier.setPatient(p);
        dossier.setMedecin(m);
        dossier.setDateDeCreation(LocalDateTime.now());
        dossier.setHistoriqueDesMaladies("Grippe");
        dossier.setStatutDossier("Ouvert");
        dossier.setOperationsPassees("Aucune");
        dossier.setConsultationsPassees("Aucune");
        dossier.setNotes("RAS");
        dossier.setImage("img.png");

        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS))).thenReturn(mockPstmt);
        when(mockPstmt.executeUpdate()).thenReturn(1);
        
        ResultSet mockKeys = mock(ResultSet.class);
        when(mockPstmt.getGeneratedKeys()).thenReturn(mockKeys);
        when(mockKeys.next()).thenReturn(true);
        when(mockKeys.getInt(1)).thenReturn(100);

        boolean result = dossierService.ajouterDossier(dossier);

        assertTrue(result);
        assertEquals(100, dossier.getId());
        verify(mockPstmt).setInt(8, 1);
        verify(mockPstmt).setInt(9, 2);
    }

    @Test
    void testRecupererDossierParId() throws SQLException {
        int dossierId = 5;
        int patientId = 10;
        int medecinId = 20;

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);

        when(mockRs.getInt("id")).thenReturn(dossierId);
        when(mockRs.getTimestamp("date_de_creation")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));
        when(mockRs.getInt("patient_id")).thenReturn(patientId);
        when(mockRs.getInt("medecin_id")).thenReturn(medecinId);
        
        when(mockRs.getString("historique_des_maladies")).thenReturn("Grippe");
        when(mockRs.getString("operations_passees")).thenReturn("Appendicite");
        when(mockRs.getString("consultations_passees")).thenReturn("Generaliste");
        when(mockRs.getString("statut_dossier")).thenReturn("Actif");
        when(mockRs.getString("notes")).thenReturn("RAS");
        when(mockRs.getString("image")).thenReturn("default.jpg");

        Patient realPatient = new Patient(); 
        realPatient.setId(patientId); 
        realPatient.setNom("Mario");
        
        Medecin realMedecin = new Medecin(); 
        realMedecin.setId(medecinId); 
        realMedecin.setNom("Dr. House");
        
        List<Users> usersList = new ArrayList<>();
        usersList.add(realPatient);
        usersList.add(realMedecin);
        
        when(mockUserService.listerUtilisateurs()).thenReturn(usersList);

        DossierMedicale result = dossierService.recupererDossierParId(dossierId, false);

        assertNotNull(result);
        assertEquals(dossierId, result.getId());
        assertEquals("Actif", result.getStatutDossier());
        assertEquals("Grippe", result.getHistoriqueDesMaladies());
        
        assertNotNull(result.getPatient());
        assertEquals("Mario", result.getPatient().getNom());
        assertEquals("Dr. House", result.getMedecin().getNom());
    }

    @Test
    void testModifierDossier() throws SQLException {
        User p = new User(); p.setId(1);
        User m = new User(); m.setId(2);

        DossierMedicale d = new DossierMedicale();
        d.setId(10);
        d.setPatient(p);
        d.setMedecin(m);
        d.setDateDeCreation(LocalDateTime.now());

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeUpdate()).thenReturn(1);

        boolean result = dossierService.modifierDossier(d);

        assertTrue(result);
        verify(mockPstmt).setInt(10, 10);
    }
    
    @Test
    void testSupprimerDossier() throws SQLException {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeUpdate()).thenReturn(1);
        
        boolean result = dossierService.supprimerDossier(55);
        
        assertTrue(result);
        verify(mockPstmt).setInt(1, 55);
    }

    @Test
    void testGetStatistiques() throws SQLException {
        when(mockConnection.createStatement()).thenReturn(mockStmt);
        
        ResultSet rsTotal = mock(ResultSet.class);
        when(mockStmt.executeQuery(contains("SELECT COUNT(*)"))).thenReturn(rsTotal);
        when(rsTotal.next()).thenReturn(true);
        when(rsTotal.getInt(1)).thenReturn(50);

        ResultSet rsStatus = mock(ResultSet.class);
        when(mockStmt.executeQuery(contains("statut_dossier"))).thenReturn(rsStatus);
        when(rsStatus.next()).thenReturn(true, false);
        when(rsStatus.getString("statut")).thenReturn("Ouvert");
        when(rsStatus.getInt("count")).thenReturn(30);

        ResultSet rsMonth = mock(ResultSet.class);
        when(mockStmt.executeQuery(contains("MONTH"))).thenReturn(rsMonth);
        when(rsMonth.next()).thenReturn(false);

        ResultSet rsMed = mock(ResultSet.class);
        when(mockStmt.executeQuery(contains("m.nom"))).thenReturn(rsMed);
        when(rsMed.next()).thenReturn(false);

        Map<String, Object> stats = dossierService.getStatistiques();

        assertEquals(50, stats.get("totalDossiers"));
        Map<String, Integer> statusStats = (Map<String, Integer>) stats.get("dossiersByStatus");
        assertEquals(30, statusStats.get("Ouvert"));
    }
}