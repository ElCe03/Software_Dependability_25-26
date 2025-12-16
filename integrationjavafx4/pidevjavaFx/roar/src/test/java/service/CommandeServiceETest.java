package service;

import entite.Commande;
import entite.Medicament;
import entite.MedicamentCommande;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.*;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
class CommandeServiceETest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    @InjectMocks
    private CommandeService commandeService;

    private Commande testCommande;
    private Medicament testMedicament;

    @BeforeEach
    void setup() throws SQLException {
        commandeService.setConnection(mockConnection);

        lenient().when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        lenient().when(mockConnection.createStatement()).thenReturn(mockStatement);
        
        lenient().when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        lenient().when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        lenient().when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);

        // ---------- Medicament ----------
        testMedicament = new Medicament();
        testMedicament.setId(1);
        testMedicament.setNom_medicament("Paracetamol");
        testMedicament.setPrix_medicament(5.0);

        testCommande = new Commande();
        testCommande.setId(0); 
        testCommande.setDate_commande(LocalDate.now());
        testCommande.setTotal_prix(50.0);
        testCommande.setQuantite(10);
        testCommande.setStatus("pending");
        testCommande.setStripeSessionId("test_session");
        
        testCommande.addMedicament(testMedicament, 5);
    }

    @AfterEach
    void cleanup() {
    }

    // ---------------- CRUD TESTS ----------------
    @Test
    @Order(1)
    void testCreateCommande() throws SQLException {
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(55);

        commandeService.create(testCommande);

        assertEquals(55, testCommande.getId()); 
        verify(mockPreparedStatement, atLeastOnce()).executeUpdate(); 
        verify(mockConnection).commit(); 
    }

    @Test
    @Order(2)
    void testReadAllCommandes() throws SQLException {
        
        when(mockResultSet.next()).thenReturn(true, false); 
        
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getDate("date_commande")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getDouble("total_prix")).thenReturn(100.0);
        when(mockResultSet.getString("status")).thenReturn("pending");

        List<Commande> commandes = commandeService.readAll();
        
        assertFalse(commandes.isEmpty());
        assertEquals(1, commandes.size());
    }

    @Test
    @Order(3)
    void testReadById() throws SQLException {
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getDate("date_commande")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getString("status")).thenReturn("pending");

        Commande c = commandeService.readById(10);
        
        assertNotNull(c);
        assertEquals(10, c.getId());
    }

    @Test
    @Order(4)
    void testUpdateCommande() throws SQLException {
        testCommande.setId(10); 
        testCommande.setStatus("completed");

        assertDoesNotThrow(() -> commandeService.update(testCommande));

        verify(mockPreparedStatement, times(1)).executeUpdate();
    }

    @Test
    @Order(5)
    void testDeleteCommande() throws SQLException {
        testCommande.setId(10);
        
        assertDoesNotThrow(() -> commandeService.delete(testCommande));

        verify(mockPreparedStatement, atLeast(2)).executeUpdate();
    }

    // ---------------- NEGATIVE / ROBUSTNESS TESTS ----------------
    @Test
    @Order(6)
    void testReadByInvalidId() throws SQLException {
        when(mockResultSet.next()).thenReturn(false);

        Commande c = commandeService.readById(-1);
        assertNull(c);
    }

    @Test
    @Order(7)
    void testDeleteNonExistingCommande() throws SQLException {
        Commande fake = new Commande();
        fake.setId(-999);
        
        assertDoesNotThrow(() -> commandeService.delete(fake));
        
        verify(mockPreparedStatement, atLeast(1)).executeUpdate();
    }
}