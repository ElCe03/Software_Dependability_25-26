package util;

import org.junit.jupiter.api.*;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
class ImageUploadUtilTest {

    private static final String UPLOAD_DIR = "uploads/images";
    private File tempSourceFile;
    private final List<String> createdFilenames = new ArrayList<>();

    @BeforeEach
    void setUp() throws IOException {
        ImageUploadUtil.initUploadDirectory();

        tempSourceFile = File.createTempFile("test_source_image", ".png");
        Files.writeString(tempSourceFile.toPath(), "Fake Image Content for Testing");
    }

    @AfterEach
    void tearDown() {
        for (String filename : createdFilenames) {
            ImageUploadUtil.deleteImage(filename);
        }

        if (tempSourceFile != null && tempSourceFile.exists()) {
            tempSourceFile.delete();
        }
    }

    @Test
    @Order(1)
    void testSaveImage_Success() {
        String originalName = "avatar.png";
        
        String newFilename = ImageUploadUtil.saveImage(tempSourceFile, originalName);
        
        if (newFilename != null) createdFilenames.add(newFilename);

        assertNotNull(newFilename, "Il nome del file generato non deve essere null");
        assertNotEquals(originalName, newFilename, "Il nome del file deve essere un UUID, non l'originale");
        assertTrue(newFilename.endsWith(".png"), "L'estensione deve essere preservata");
        
        assertTrue(ImageUploadUtil.imageExists(newFilename), "Il file deve esistere fisicamente su disco");
    }

    @Test
    @Order(2)
    void testSaveImage_PreservesExtension() {
        String originalName = "document.pdf.jpg";
        
        String newFilename = ImageUploadUtil.saveImage(tempSourceFile, originalName);
        createdFilenames.add(newFilename);

        assertNotNull(newFilename);
        assertTrue(newFilename.endsWith(".jpg"), "Deve prendere l'ultima estensione disponibile");
    }

    @Test
    @Order(3)
    void testSaveImage_NoExtension() {
        String originalName = "README"; 
        
        String newFilename = ImageUploadUtil.saveImage(tempSourceFile, originalName);
        createdFilenames.add(newFilename);

        assertNotNull(newFilename);
        assertFalse(newFilename.contains("."), "Se non c'è estensione, il file generato non deve averne");
        assertEquals(36, newFilename.length(), "La lunghezza di un UUID standard è 36 caratteri");
    }

    @Test
    @Order(4)
    void testDeleteImage_Success() {
        String savedFile = ImageUploadUtil.saveImage(tempSourceFile, "to_delete.png");
        assertTrue(ImageUploadUtil.imageExists(savedFile));

        boolean deleted = ImageUploadUtil.deleteImage(savedFile);

        assertTrue(deleted, "Il metodo deve ritornare true se il file è stato cancellato");
        assertFalse(ImageUploadUtil.imageExists(savedFile), "Il file non deve più esistere su disco");
    }

    @Test
    @Order(5)
    void testDeleteImage_NotFound() {
        boolean result = ImageUploadUtil.deleteImage("non_existent_ghost_file.jpg");
        assertFalse(result, "Deve ritornare false se il file non esiste");
    }

    @Test
    @Order(6)
    void testEdgeCases_NullOrEmpty() {

        assertFalse(ImageUploadUtil.deleteImage(null));
        assertFalse(ImageUploadUtil.deleteImage(""));

        assertFalse(ImageUploadUtil.imageExists(null));
        assertFalse(ImageUploadUtil.imageExists(""));

        assertNull(ImageUploadUtil.getImagePath(null));
        assertNull(ImageUploadUtil.getImagePath(""));
    }

    @Test
    @Order(7)
    void testGetImagePath() {
        String filename = "test-image.jpg";
        String path = ImageUploadUtil.getImagePath(filename);

        assertNotNull(path);
        assertTrue(path.contains("uploads"), "Il path deve contenere 'uploads'");
        assertTrue(path.contains("images"), "Il path deve contenere 'images'");
        assertTrue(path.endsWith(filename), "Il path deve terminare con il nome del file");
        
        File f = new File(path);
        assertTrue(f.isAbsolute(), "Il path restituito deve essere assoluto");
    }
    
    @Test
    @Order(8)
    void testInitDirectoryIsIdempotent() {
        assertDoesNotThrow(ImageUploadUtil::initUploadDirectory);
        
        File dir = new File(UPLOAD_DIR);
        assertTrue(dir.exists());
        assertTrue(dir.isDirectory());
    }
    @Test
    @Order(9)
    void testSaveImage_ContentIntegrity() throws IOException {
        String content = "Critical Medical Data Checksum 12345";
        File integritySource = File.createTempFile("integrity_test", ".txt");
        Files.writeString(integritySource.toPath(), content);

        String savedFilename = ImageUploadUtil.saveImage(integritySource, "scan.txt");
        createdFilenames.add(savedFilename);

        assertNotNull(savedFilename);
        
        Path savedPath = Paths.get(UPLOAD_DIR, savedFilename);
        String savedContent = Files.readString(savedPath);

        assertEquals(content, savedContent, "Il contenuto del file salvato deve essere identico all'originale");
        
        integritySource.delete();
    }


    @Test
    @Order(10)
    void testSaveImage_SourceFileNotFound() {
        File missingFile = new File("ghost_file_xyz.png");

        String result = ImageUploadUtil.saveImage(missingFile, "ghost.png");

        assertNull(result, "Se il file sorgente non esiste, il metodo deve ritornare null");
    }


    @Test
    @Order(11)
    void testSaveImage_DotFiles() {
        String originalName = ".env"; 
        
        String newFilename = ImageUploadUtil.saveImage(tempSourceFile, originalName);
        createdFilenames.add(newFilename);

        assertNotNull(newFilename);
        assertFalse(newFilename.contains("."), "I dotfiles (es. .env) non dovrebbero generare estensioni errate");
        assertEquals(36, newFilename.length());
    }

    @Test
    @Order(12)
    void testSaveImage_PathTraversalAttempt() {
        String maliciousName = "../../../etc/passwd.jpg";
        
        String newFilename = ImageUploadUtil.saveImage(tempSourceFile, maliciousName);
        createdFilenames.add(newFilename);

        assertNotNull(newFilename);

        Path targetPath = Paths.get(UPLOAD_DIR, newFilename);
        assertTrue(Files.exists(targetPath), "Il file deve essere salvato nella directory uploads, neutralizzando il path traversal");
        assertTrue(newFilename.endsWith(".jpg"));
    }

    @Test
    @Order(13)
    void testSaveImage_BulkUpload() {
        int count = 50;
        List<String> bulkFiles = new ArrayList<>();

        for (int i = 0; i < count; i++) {
            String name = ImageUploadUtil.saveImage(tempSourceFile, "img_" + i + ".png");
            if (name != null) {
                bulkFiles.add(name);
                createdFilenames.add(name); 
            }
        }

        assertEquals(count, bulkFiles.size(), "Tutti i 50 file dovrebbero essere stati salvati correttamente");
        
        long uniqueCount = bulkFiles.stream().distinct().count();
        assertEquals(count, uniqueCount, "Ogni file salvato deve avere un UUID univoco");
    }
}