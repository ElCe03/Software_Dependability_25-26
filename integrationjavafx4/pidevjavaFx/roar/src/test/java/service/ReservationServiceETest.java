package service;

import entite.reservation;
import entite.salle;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class ReservationServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private ReservationService service;

    @BeforeEach
    void setup() throws SQLException {
        service.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        lenient().when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
    }

    @Test
    void testAddReservation() throws SQLException {
        reservation r = new reservation();
        salle s = new salle();
        s.setId(1);
        r.setSalle(s);
        r.setDate_debut(Timestamp.valueOf(LocalDateTime.now()));
        r.setDate_fin(Timestamp.valueOf(LocalDateTime.now().plusHours(2)));

        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(100);

        service.addReservation(mockConnection, r);

        verify(mockPreparedStatement).executeUpdate();
        assertEquals(100, r.getId());
    }

    @Test
    void testGetReservationsForSalle() throws Exception {
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getTimestamp("date_debut")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));
        when(mockResultSet.getTimestamp("date_fin")).thenReturn(Timestamp.valueOf(LocalDateTime.now().plusHours(1)));

        List<reservation> list = service.getReservationsForSalle(1);
        
        assertNotNull(list);
        assertFalse(list.isEmpty());
        assertEquals(10, list.get(0).getId());
    }

    @Test
    void testGetAllReservations() throws Exception {
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("id")).thenReturn(5);
        when(mockResultSet.getInt("salle_id")).thenReturn(2);
        when(mockResultSet.getString("salle_nom")).thenReturn("Salle A");
        when(mockResultSet.getString("salle_status")).thenReturn("Occupée");
        when(mockResultSet.getInt("capacite")).thenReturn(50);
        when(mockResultSet.getString("type_salle")).thenReturn("Conférence");
        when(mockResultSet.getTimestamp("date_debut")).thenReturn(Timestamp.valueOf(LocalDateTime.now()));
        when(mockResultSet.getTimestamp("date_fin")).thenReturn(Timestamp.valueOf(LocalDateTime.now().plusHours(2)));

        List<reservation> list = service.getAllReservations();
        
        assertNotNull(list);
        assertFalse(list.isEmpty());
        assertEquals("Salle A", list.get(0).getSalle().getNom());
    }

    @Test
    void testTerminerReservation() throws Exception {
        doNothing().when(mockConnection).setAutoCommit(false);
        doNothing().when(mockConnection).commit();

        service.terminerReservation(mockConnection, 123);

        verify(mockConnection, times(2)).prepareStatement(anyString());
        verify(mockPreparedStatement, times(2)).executeUpdate();
        verify(mockConnection).commit();
    }
}