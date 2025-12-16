package service;

import entite.Sejour;
import javafx.stage.Stage;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.File;
import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class PDFServiceTest {

    @Mock
    private PDFService.FileSelectionStrategy mockFileSelectionStrategy;

    @Mock
    private PDFService.AlertStrategy mockAlertStrategy;

    private PDFService pdfService;
    private List<Sejour> mockSejours;

    @BeforeEach
    void setUp() {
        pdfService = new PDFService(mockFileSelectionStrategy, mockAlertStrategy);

        mockSejours = new ArrayList<>();
        
        Sejour s1 = new Sejour();
        s1.setId(1);
        s1.setDateEntree(LocalDateTime.now().minusDays(5));
        s1.setDateSortie(LocalDateTime.now());
        s1.setTypeSejour("Hospitalisation");
        s1.setFraisSejour(500.0);
        s1.setPrixExtras(50.0);
        s1.setMoyenPaiement("Carte");
        s1.setStatutPaiement("Payé");
        mockSejours.add(s1);
        Sejour s2 = new Sejour();
        s2.setId(2);
        s2.setTypeSejour("Consultation");
        s2.setFraisSejour(100.0);
        s2.setPrixExtras(0.0);
        s2.setStatutPaiement("En attente");
        mockSejours.add(s2);
    }

    @Test
    void testGenerateSejourAnalysisPDF_Success() throws IOException {
        File tempFile = File.createTempFile("test_report", ".pdf");
        tempFile.deleteOnExit();

        when(mockFileSelectionStrategy.selectFile(any(), anyString())).thenReturn(tempFile);

        pdfService.generateSejourAnalysisPDF(mockSejours, null);

        verify(mockAlertStrategy).showInformation(any(), anyString(), anyString());
        
        assertTrue(tempFile.exists(), "Il file PDF dovrebbe esistere");
        assertTrue(tempFile.length() > 0, "Il file PDF non dovrebbe essere vuoto");
    }

    @Test
    void testGenerateSejourAnalysisPDF_UserCancelled() {
        when(mockFileSelectionStrategy.selectFile(any(), anyString())).thenReturn(null);

        pdfService.generateSejourAnalysisPDF(mockSejours, null);

        verify(mockAlertStrategy, never()).showInformation(any(), any(), any());
        verify(mockAlertStrategy, never()).showError(any(), any(), any());
    }

    @Test
    void testGenerateSejourAnalysisPDF_FileNotFoundException() {
        File directory = new File(System.getProperty("java.io.tmpdir"));
        
        when(mockFileSelectionStrategy.selectFile(any(), anyString())).thenReturn(directory);

        pdfService.generateSejourAnalysisPDF(mockSejours, null);

        verify(mockAlertStrategy).showError(any(), anyString(), anyString());
    }
}