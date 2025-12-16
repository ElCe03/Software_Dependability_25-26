package service;

import entite.Consultation;
import org.junit.jupiter.api.AfterEach; // Ajout de l'import pour le nettoyage
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
public class ConsultationServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private ConsultationService service;

    private int consultationId = 10; // ID de la consultation créée pour le test

    @BeforeEach
    void setup() throws Exception {
        service.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.createStatement()).thenReturn(mockStatement);
        
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
    }

    @AfterEach
    void tearDown() {
    }

    @Test
    void testGetAllConsultations() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, false); 
        
        when(mockResultSet.getInt("id")).thenReturn(consultationId);
        when(mockResultSet.getInt("service_id")).thenReturn(1);
        when(mockResultSet.getString("service_name")).thenReturn("Test Service");
        when(mockResultSet.getDate("date")).thenReturn(Date.valueOf("2025-01-01"));
        when(mockResultSet.getString("patient_identifier")).thenReturn("PATIENT_TEST_001");
        when(mockResultSet.getString("status")).thenReturn("En cours");
        when(mockResultSet.getString("phone_number")).thenReturn("22334455");

        List<Consultation> list = service.getAllConsultations();
        assertNotNull(list, "La liste de consultations ne doit pas être null.");
        // Vérifie qu'au moins la consultation créée est présente
        assertTrue(list.size() > 0, "La liste doit contenir au moins la consultation de test.");

        // Vérification plus stricte
        Consultation createdConsultation = list.stream()
                .filter(c -> c.getId() == consultationId)
                .findFirst()
                .orElse(null);
        assertNotNull(createdConsultation, "La consultation créée doit être trouvée dans la liste complète.");
    }

    @Test
    void testSearchConsultation() throws SQLException {
        when(mockResultSet.next()).thenReturn(true, false);
        
        when(mockResultSet.getInt("id")).thenReturn(consultationId);
        when(mockResultSet.getInt("service_id")).thenReturn(1);
        when(mockResultSet.getString("service_name")).thenReturn("Test Service");
        when(mockResultSet.getDate("date")).thenReturn(Date.valueOf("2025-01-01"));
        when(mockResultSet.getString("patient_identifier")).thenReturn("PATIENT_TEST_001");
        when(mockResultSet.getString("status")).thenReturn("En cours");
        when(mockResultSet.getString("phone_number")).thenReturn("22334455");

        List<Consultation> list = service.searchConsultations("PATIENT_TEST");

        assertNotNull(list, "Le résultat de la recherche ne doit pas être null.");
        assertTrue(list.size() > 0, "La recherche doit retourner au moins une consultation.");

        // Vérification spécifique que notre consultation de test est bien trouvée
        boolean found = list.stream().anyMatch(c -> c.getId() == consultationId);
        assertTrue(found, "La recherche sur 'PATIENT_TEST' doit trouver la consultation créée.");
    }

    @Test
    void testUpdateStatus() throws SQLException {
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        String newStatus = "Terminée";
        boolean updated = service.updateConsultationStatus(consultationId, newStatus);

        assertTrue(updated, "L'update du statut doit retourner true.");
        verify(mockPreparedStatement, times(1)).executeUpdate();
    }
}