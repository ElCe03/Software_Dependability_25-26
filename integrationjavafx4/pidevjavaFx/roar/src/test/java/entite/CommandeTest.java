package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class CommandeTest {

    @Mock
    private Medicament medicamentMockA;

    @Mock
    private Medicament medicamentMockB;

    @Test
    void testDefaultConstructor() {
        Commande cmd = new Commande();

        assertEquals(0, cmd.getId());
        assertEquals(0.0, cmd.getTotal_prix());
        assertEquals(0, cmd.getQuantite());
        assertNotNull(cmd.getMedicaments());
        assertTrue(cmd.getMedicaments().isEmpty());
    }

    @Test
    void testParameterizedConstructor() {
        LocalDate date = LocalDate.now();
        Commande cmd = new Commande(10, date, 150.50, 5);

        assertEquals(10, cmd.getId());
        assertEquals(date, cmd.getDate_commande());
        assertEquals(150.50, cmd.getTotal_prix());
        assertEquals(5, cmd.getQuantite());
        assertNotNull(cmd.getMedicaments());
    }

    @Test
    void testAddMedicament() {
        Commande cmd = new Commande();
        int quantity = 2;

        cmd.addMedicament(medicamentMockA, quantity);

        List<MedicamentCommande> list = cmd.getMedicaments();
        
        assertEquals(1, list.size());
        assertEquals(medicamentMockA, list.get(0).getMedicament());
    }

    @Test
    void testGetNomMedicamentsCommandes() {
        Commande cmd = new Commande();
        
        when(medicamentMockA.getNom_medicament()).thenReturn("Aspirina");
        when(medicamentMockB.getNom_medicament()).thenReturn("Oki");

        cmd.addMedicament(medicamentMockA, 1);
        cmd.addMedicament(medicamentMockB, 2);
        
        String result = cmd.getNomMedicamentsCommandes();

        assertEquals("Aspirina, Oki", result);
        
        verify(medicamentMockA, times(1)).getNom_medicament();
        verify(medicamentMockB, times(1)).getNom_medicament();
    }

    @Test
    void testGetNomMedicamentsCommandesEmpty() {
        Commande cmd = new Commande();
        assertEquals("", cmd.getNomMedicamentsCommandes());
    }
    
    @Test
    void testSettersAndGetters() {
        Commande cmd = new Commande();
        
        cmd.setStripeSessionId("sess_123");
        cmd.setStatus("PAID");
        cmd.setTotal_prix(99.99);
        cmd.setQuantite(10);
        cmd.setId(5);
        LocalDate date = LocalDate.of(2023, 10, 1);
        cmd.setDate_commande(date);
        
        assertAll(
            () -> assertEquals("sess_123", cmd.getStripeSessionId()),
            () -> assertEquals("PAID", cmd.getStatus()),
            () -> assertEquals(99.99, cmd.getTotal_prix()),
            () -> assertEquals(10, cmd.getQuantite()),
            () -> assertEquals(5, cmd.getId()),
            () -> assertEquals(date, cmd.getDate_commande())
        );
    }
}