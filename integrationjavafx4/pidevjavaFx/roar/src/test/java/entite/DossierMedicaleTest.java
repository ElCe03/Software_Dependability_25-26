package entite;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class DossierMedicaleTest {

    @Mock
    private User patientMock;

    @Mock
    private User medecinMock;

    @Mock
    private Sejour sejourMock;

    @Test
    void testDefaultConstructor() {
        DossierMedicale dossier = new DossierMedicale();

        assertEquals(0, dossier.getId());
        assertNotNull(dossier.getSejours());
        assertTrue(dossier.getSejours().isEmpty());
        assertNull(dossier.getPatient());
        assertNull(dossier.getMedecin());
    }

    @Test
    void testParameterizedConstructor() {
        LocalDateTime now = LocalDateTime.now();
        DossierMedicale dossier = new DossierMedicale(
            patientMock, medecinMock, now, 
            "Hist", "Ops", "Cons", 
            "Open", "Notes", "Img.jpg"
        );

        assertEquals(patientMock, dossier.getPatient());
        assertEquals(medecinMock, dossier.getMedecin());
        assertEquals(now, dossier.getDateDeCreation());
        assertEquals("Hist", dossier.getHistoriqueDesMaladies());
        assertEquals("Ops", dossier.getOperationsPassees());
        assertEquals("Cons", dossier.getConsultationsPassees());
        assertEquals("Open", dossier.getStatutDossier());
        assertEquals("Notes", dossier.getNotes());
        assertEquals("Img.jpg", dossier.getImage());
        assertNotNull(dossier.getSejours());
        assertTrue(dossier.getSejours().isEmpty());
    }

    @Test
    void testGetPatientIdNullSafe() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setPatient(null);

        assertEquals(0, dossier.getPatientId());
    }

    @Test
    void testGetPatientIdWithUser() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setPatient(patientMock);
        
        when(patientMock.getId()).thenReturn(123);

        assertEquals(123, dossier.getPatientId());
    }

    @Test
    void testGetMedecinIdNullSafe() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setMedecin(null);

        assertEquals(0, dossier.getMedecinId());
    }

    @Test
    void testGetMedecinIdWithUser() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setMedecin(medecinMock);
        
        when(medecinMock.getId()).thenReturn(456);

        assertEquals(456, dossier.getMedecinId());
    }

    @Test
    void testAddSejourUpdatesRelationship() {
        DossierMedicale dossier = new DossierMedicale();
        
        when(sejourMock.getDossierMedicale()).thenReturn(null);

        dossier.addSejour(sejourMock);

        List<Sejour> sejours = dossier.getSejours();
        assertEquals(1, sejours.size());
        assertEquals(sejourMock, sejours.get(0));

        verify(sejourMock, times(1)).setDossierMedicale(dossier);
    }

    @Test
    void testAddSejourAvoidsInfiniteLoop() {
        DossierMedicale dossier = new DossierMedicale();
        
        when(sejourMock.getDossierMedicale()).thenReturn(dossier);

        dossier.addSejour(sejourMock);

        assertEquals(1, dossier.getSejours().size());
        
        verify(sejourMock, never()).setDossierMedicale(any());
    }

    @Test
    void testAddSejourInitializeListIfNull() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setSejours(null); 
        
        when(sejourMock.getDossierMedicale()).thenReturn(null);
        
        dossier.addSejour(sejourMock);
        
        assertNotNull(dossier.getSejours());
        assertEquals(1, dossier.getSejours().size());
    }

    @Test
    void testSettersAndGettersSimple() {
        DossierMedicale dossier = new DossierMedicale();
        
        dossier.setId(99);
        dossier.setHistoriqueDesMaladies("H");
        dossier.setOperationsPassees("O");
        dossier.setConsultationsPassees("C");
        dossier.setStatutDossier("S");
        dossier.setNotes("N");
        dossier.setImage("I");
        LocalDateTime date = LocalDateTime.now();
        dossier.setDateDeCreation(date);

        assertAll(
            () -> assertEquals(99, dossier.getId()),
            () -> assertEquals("H", dossier.getHistoriqueDesMaladies()),
            () -> assertEquals("O", dossier.getOperationsPassees()),
            () -> assertEquals("C", dossier.getConsultationsPassees()),
            () -> assertEquals("S", dossier.getStatutDossier()),
            () -> assertEquals("N", dossier.getNotes()),
            () -> assertEquals("I", dossier.getImage()),
            () -> assertEquals(date, dossier.getDateDeCreation())
        );
    }

    @Test
    void testToString() {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setId(5);
        assertEquals("Dossier #5", dossier.toString());
    }
}