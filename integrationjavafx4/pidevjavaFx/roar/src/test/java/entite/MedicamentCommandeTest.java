package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
class MedicamentCommandeTest {

    @Mock
    private Commande commandeMock;

    @Mock
    private Medicament medicamentMock;

    @Mock
    private Commande newCommandeMock;

    @Test
    void testConstructorAndGetters() {
        int quantite = 10;
        MedicamentCommande mc = new MedicamentCommande(commandeMock, medicamentMock, quantite);

        assertEquals(commandeMock, mc.getCommande());
        assertEquals(medicamentMock, mc.getMedicament());
        assertEquals(quantite, mc.getQuantite());
    }

    @Test
    void testSetCommande() {
        MedicamentCommande mc = new MedicamentCommande(commandeMock, medicamentMock, 5);

        mc.setCommande(newCommandeMock);

        assertEquals(newCommandeMock, mc.getCommande());
        assertNotEquals(commandeMock, mc.getCommande());
    }

    @Test
    void testObjectIdentity() {
        MedicamentCommande mc1 = new MedicamentCommande(commandeMock, medicamentMock, 1);
        MedicamentCommande mc2 = new MedicamentCommande(commandeMock, medicamentMock, 1);

        assertNotSame(mc1, mc2);
        assertEquals(mc1.getQuantite(), mc2.getQuantite());
        assertEquals(mc1.getMedicament(), mc2.getMedicament());
    }
}