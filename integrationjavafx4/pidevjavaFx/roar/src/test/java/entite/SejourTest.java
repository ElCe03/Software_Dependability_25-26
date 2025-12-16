package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class SejourTest {

    @Mock
    private DossierMedicale dossierMock;

    @Test
    void testDefaultConstructor() {
        Sejour sejour = new Sejour();

        assertEquals(0, sejour.getId());
        assertEquals(0.0, sejour.getFraisSejour());
        assertEquals(0.0, sejour.getPrixExtras());
        assertEquals("En attente", sejour.getStatutPaiement());
        assertNull(sejour.getDateEntree());
        assertNull(sejour.getDateSortie());
        assertNull(sejour.getDossierMedicale());
    }

    @Test
    void testParameterizedConstructor() {
        LocalDateTime entree = LocalDateTime.of(2023, 10, 1, 10, 0);
        LocalDateTime sortie = LocalDateTime.of(2023, 10, 5, 12, 0);
        String type = "Chirurgie";
        double frais = 1000.0;
        String moyen = "Carte";
        String statut = "Payé";
        double extras = 50.0;

        Sejour sejour = new Sejour(entree, sortie, type, frais, moyen, statut, extras, dossierMock);

        assertEquals(entree, sejour.getDateEntree());
        assertEquals(sortie, sejour.getDateSortie());
        assertEquals(type, sejour.getTypeSejour());
        assertEquals(frais, sejour.getFraisSejour());
        assertEquals(moyen, sejour.getMoyenPaiement());
        assertEquals(statut, sejour.getStatutPaiement());
        assertEquals(extras, sejour.getPrixExtras());
        assertEquals(dossierMock, sejour.getDossierMedicale());
    }

    @Test
    void testSetDossierMedicaleBiDirectionalLogic() {
        Sejour sejour = new Sejour();
        
        when(dossierMock.getSejours()).thenReturn(new ArrayList<>());

        sejour.setDossierMedicale(dossierMock);

        assertEquals(dossierMock, sejour.getDossierMedicale());
        verify(dossierMock, times(1)).addSejour(sejour);
    }

    @Test
    void testSetDossierMedicaleAvoidsDuplication() {
        Sejour sejour = new Sejour();
        List<Sejour> existingList = new ArrayList<>();
        existingList.add(sejour);

        when(dossierMock.getSejours()).thenReturn(existingList);

        sejour.setDossierMedicale(dossierMock);

        verify(dossierMock, never()).addSejour(sejour);
    }

    @Test
    void testGetDossierMedicaleId() {
        Sejour sejour = new Sejour();
        
        assertEquals(0, sejour.getDossierMedicaleId());

        when(dossierMock.getId()).thenReturn(123);
        
        // Simuliamo il comportamento di base per evitare NPE nel setter
        when(dossierMock.getSejours()).thenReturn(new ArrayList<>());
        
        sejour.setDossierMedicale(dossierMock);
        assertEquals(123, sejour.getDossierMedicaleId());
    }

    @Test
    void testCalculateTotalCost() {
        Sejour sejour = new Sejour();
        sejour.setFraisSejour(500.50);
        sejour.setPrixExtras(99.50);

        assertEquals(600.00, sejour.calculateTotalCost());
    }

    @Test
    void testCalculateStayDurationValid() {
        Sejour sejour = new Sejour();
        sejour.setDateEntree(LocalDateTime.of(2023, 1, 1, 12, 0));
        sejour.setDateSortie(LocalDateTime.of(2023, 1, 5, 10, 0));

        assertEquals(4, sejour.calculateStayDuration());
    }

    @Test
    void testCalculateStayDurationNullDates() {
        Sejour sejour = new Sejour();
        
        sejour.setDateEntree(LocalDateTime.now());
        assertEquals(0, sejour.calculateStayDuration());

        sejour.setDateEntree(null);
        sejour.setDateSortie(LocalDateTime.now());
        assertEquals(0, sejour.calculateStayDuration());
    }

    @Test
    void testTransientFields() {
        Sejour sejour = new Sejour();
        
        sejour.setChambre("101-A");
        sejour.setNotes("Patient fragile");

        assertEquals("101-A", sejour.getChambre());
        assertEquals("Patient fragile", sejour.getNotes());
    }

    @Test
    void testToString() {
        Sejour sejour = new Sejour();
        sejour.setId(7);
        sejour.setTypeSejour("Urgence");
        
        String result = sejour.toString();
        
        assertTrue(result.contains("Séjour #7"));
        assertTrue(result.contains("Urgence"));
        assertTrue(result.contains("N/A")); 
    }
}