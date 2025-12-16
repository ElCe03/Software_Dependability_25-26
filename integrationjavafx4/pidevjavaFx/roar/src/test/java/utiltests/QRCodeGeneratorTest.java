package util;

import com.google.zxing.WriterException;
import javafx.application.Platform;
import javafx.scene.image.Image;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable; 

import java.io.IOException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

class QRCodeGeneratorTest {

    @BeforeAll
    static void initJavaFX() throws InterruptedException {

        try {
            CountDownLatch latch = new CountDownLatch(1);
            Platform.startup(latch::countDown);
            if (!latch.await(5, TimeUnit.SECONDS)) {
                System.err.println("Warning: JavaFX Platform failed to start (expected in CI without Headless config)");
            }
        } catch (IllegalStateException e) {
        } catch (UnsupportedOperationException e) {
            System.err.println("JavaFX non supportato in questo ambiente.");
        }
    }

    @Test
    void testGenerateQRCodeBytes_Success() throws IOException, WriterException {
        String text = "SoftwareDependabilityProject2025";
        int size = 200;

        byte[] result = QRCodeGenerator.generateQRCodeBytes(text, size, size);

        assertNotNull(result, "Il risultato non deve essere null");
        assertTrue(result.length > 0, "Il byte array deve contenere dati");

        if (result.length > 8) {
            assertEquals((byte) 0x89, result[0]);
            assertEquals((byte) 0x50, result[1]); 
            assertEquals((byte) 0x4E, result[2]); 
            assertEquals((byte) 0x47, result[3]); 
        }
    }

    @Test
    @DisabledIfEnvironmentVariable(named = "CI", matches = "true") 
    void testGenerateQRCodeImage_Success() throws IOException, WriterException {
        String text = "JavaFXTest";
        int width = 250;
        int height = 250;


        try {
            Platform.runLater(() -> {}); 
        } catch (IllegalStateException e) {
            org.junit.jupiter.api.Assumptions.assumeTrue(false, "JavaFX Toolkit not initialized - Skipping UI test");
        }

        Image fxImage = QRCodeGenerator.generateQRCodeImage(text, width, height);

        assertNotNull(fxImage, "L'immagine JavaFX generata non deve essere null");
        assertFalse(fxImage.isError(), "L'immagine non deve riportare errori");
        assertTrue(fxImage.getWidth() > 0);
        assertTrue(fxImage.getHeight() > 0);
    }

    
    @Test
    void testGenerateQRCode_EmptyText() {
        assertThrows(Exception.class, () -> 
            QRCodeGenerator.generateQRCodeBytes("", 200, 200));
    }

    @Test
    void testGenerateQRCode_NegativeDimensions() {
        assertThrows(IllegalArgumentException.class, () -> 
            QRCodeGenerator.generateQRCodeBytes("Test", -100, -100));
    }
    @Test
    void testGenerateQRCodeBytes_IsValidImage() throws IOException, WriterException {
        String text = "IntegrityCheck";
        byte[] imageBytes = QRCodeGenerator.generateQRCodeBytes(text, 200, 200);

        try (java.io.ByteArrayInputStream bis = new java.io.ByteArrayInputStream(imageBytes)) {
            java.awt.image.BufferedImage bufferedImage = javax.imageio.ImageIO.read(bis);
            
            assertNotNull(bufferedImage, "I byte generati dovrebbero essere decodificabili in un'immagine valida");
            assertEquals(200, bufferedImage.getWidth(), "La larghezza dell'immagine decodificata deve corrispondere");
            assertEquals(200, bufferedImage.getHeight(), "L'altezza dell'immagine decodificata deve corrispondere");
        }
    }


    @Test
    void testGenerateQRCode_SpecialCharacters() throws IOException, WriterException {
        String text = "Mèdico & Patiënt -> 🏥 💊";
        
        byte[] result = QRCodeGenerator.generateQRCodeBytes(text, 250, 250);
        
        assertNotNull(result);
        assertTrue(result.length > 0);
    }


    @Test
    void testGenerateQRCode_JsonContent() throws IOException, WriterException {
        String jsonPayload = "{\"id\":123, \"type\":\"consultation\", \"date\":\"2025-10-10\"}";
        
        byte[] result = QRCodeGenerator.generateQRCodeBytes(jsonPayload, 300, 300);
        
        assertNotNull(result);
        assertTrue(result.length > 100, "Un payload JSON dovrebbe generare un file di dimensioni significative");
    }


    @Test
    void testGenerateQRCode_HighDensityURL() throws IOException, WriterException {
        String baseUrl = "https://clinique-app.com/validation/token?v=";
        String longToken = "a".repeat(200); 
        String fullUrl = baseUrl + longToken;

        byte[] result = QRCodeGenerator.generateQRCodeBytes(fullUrl, 500, 500);

        assertNotNull(result);
        try (java.io.ByteArrayInputStream bis = new java.io.ByteArrayInputStream(result)) {
            assertNotNull(javax.imageio.ImageIO.read(bis));
        }
    }

    @Test
    void testGenerateQRCode_SmallSize() throws IOException, WriterException {
        String text = "A";

        byte[] result = QRCodeGenerator.generateQRCodeBytes(text, 20, 20);
        
        assertNotNull(result);
        try (java.io.ByteArrayInputStream bis = new java.io.ByteArrayInputStream(result)) {
            var img = javax.imageio.ImageIO.read(bis);
            assertNotNull(img);
            assertTrue(img.getWidth() > 0);
        }
    }
}