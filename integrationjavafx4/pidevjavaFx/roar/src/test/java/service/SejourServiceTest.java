package test;

import entite.DossierMedicale;
import entite.Sejour;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import service.SejourService;

import java.sql.*;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class SejourServiceTest {

    @Mock
    private Connection mockConnection;

    @Mock
    private PreparedStatement mockPreparedStatement;

    @Mock
    private ResultSet mockResultSet;

    private SejourService sejourService;

    @BeforeEach
    void setUp() throws SQLException {
        sejourService = new SejourService(mockConnection);
    }

    @Test
    void testAjouterSejour_Success() throws SQLException {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setId(1);

        Sejour sejour = new Sejour();
        sejour.setDossierMedicale(dossier);
        sejour.setFraisSejour(100.0);
        sejour.setPrixExtras(50.0);
        sejour.setDateEntree(LocalDateTime.now());

        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPreparedStatement);
        
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(99); 

        boolean result = sejourService.ajouterSejour(sejour);

        assertTrue(result, "L'aggiunta del soggiorno dovrebbe avere successo");
        assertEquals(99, sejour.getId(), "L'ID del soggiorno dovrebbe essere stato aggiornato dal DB mock");
        
        verify(mockConnection).prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS));
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testAjouterSejour_FraisNegatifs() {
        Sejour sejour = new Sejour();
        sejour.setFraisSejour(-10.0); 

        boolean result = sejourService.ajouterSejour(sejour);

        assertFalse(result, "L'aggiunta dovrebbe fallire con spese negative");
        verifyNoInteractions(mockConnection);
    }
    
    @Test
    void testAjouterSejour_DateInvalide() {
        Sejour sejour = new Sejour();
        sejour.setDateEntree(LocalDateTime.now());
        sejour.setDateSortie(LocalDateTime.now().minusDays(1)); 

        boolean result = sejourService.ajouterSejour(sejour);

        assertFalse(result, "L'aggiunta dovrebbe fallire se la data di uscita è precedente all'entrata");
        verifyNoInteractions(mockConnection);
    }

    @Test
    void testModifierSejour_Success() throws SQLException {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setId(1);
        Sejour sejour = new Sejour();
        sejour.setId(10);
        sejour.setDossierMedicale(dossier);
        sejour.setFraisSejour(200.0);
        sejour.setDateEntree(LocalDateTime.now());

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        boolean result = sejourService.modifierSejour(sejour);

        assertTrue(result);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testRecupererSejourParId_Trovato() throws SQLException {
        int idCercato = 5;
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(idCercato);
        when(mockResultSet.getDouble("frais_sejour")).thenReturn(150.0);
        when(mockResultSet.getTimestamp("date_entree")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));

        Sejour result = sejourService.recupererSejourParId(idCercato);

        assertNotNull(result);
        assertEquals(idCercato, result.getId());
    }
}