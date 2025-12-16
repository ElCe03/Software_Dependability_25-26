package utiltests; 

import com.google.gson.JsonSyntaxException;
import entite.Appointment;
import org.junit.jupiter.api.*;
import util.AppointmentPersistence;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
class AppointmentPersistenceTest {

    private static final String FILENAME = "appointments.json";
    private List<Appointment> sampleList;

    @BeforeEach
    void setUp() {
        // 1. Pulizia preventiva
        deletePersistenceFile();

        // 2. Creazione dati di prova
        sampleList = new ArrayList<>();
        
        // Uso il costruttore corretto a 5 argomenti: Title, Description, Start, End, Group
        Appointment a1 = new Appointment(
            "Consultation Cardiologie", 
            "Suivi patient annuel",
            LocalDateTime.of(2025, 10, 10, 14, 30),
            LocalDateTime.of(2025, 10, 10, 15, 0),
            "Medical"
        );
        
        sampleList.add(a1);
    }

    @AfterEach
    void tearDown() {
        // 3. Pulizia finale
        deletePersistenceFile();
    }

    private void deletePersistenceFile() {
        File file = new File(FILENAME);
        if (file.exists()) {
            boolean deleted = file.delete();
            if (!deleted) {
                System.err.println("Warning: Impossibile cancellare " + FILENAME + " durante il test cleanup.");
            }
        }
    }

    // ✅ TEST 1: Round Trip (Salvataggio e Caricamento)
    @Test
    @Order(1)
    @DisplayName("Salvataggio e ricaricamento: i dati devono corrispondere")
    void testSaveAndLoad_RoundTrip() {
        // A. Salvataggio
        AppointmentPersistence.saveAppointments(sampleList);

        // B. Verifica esistenza file
        File file = new File(FILENAME);
        assertTrue(file.exists(), "Il file JSON deve essere creato");
        assertTrue(file.length() > 0, "Il file non deve essere vuoto");

        // C. Caricamento
        List<Appointment> loadedList = AppointmentPersistence.loadAppointments();

        // D. Verifiche Contenuto
        assertNotNull(loadedList);
        assertEquals(1, loadedList.size());

        Appointment original = sampleList.get(0);
        Appointment loaded = loadedList.get(0);

        // Verifica campo per campo (poiché Appointment non ha equals/hashCode implementati per i valori)
        assertEquals(original.getTitle(), loaded.getTitle());
        assertEquals(original.getDescription(), loaded.getDescription());
        assertEquals(original.getGroup(), loaded.getGroup());
        
        // Verifica Date (importante per verificare che l'Adapter Gson funzioni)
        assertEquals(original.getStart(), loaded.getStart(), "Data inizio non corrispondente");
        assertEquals(original.getEnd(), loaded.getEnd(), "Data fine non corrispondente");
    }

    // ✅ TEST 2: File Inesistente
    @Test
    @Order(2)
    @DisplayName("Caricamento senza file: deve ritornare lista vuota")
    void testLoad_FileDoesNotExist() {
        deletePersistenceFile(); // Sicurezza

        List<Appointment> result = AppointmentPersistence.loadAppointments();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // ✅ TEST 3: Sovrascrittura
    @Test
    @Order(3)
    @DisplayName("Salvataggio successivo: deve sovrascrivere")
    void testSave_OverwritesExistingData() {
        // 1. Salvataggio iniziale
        AppointmentPersistence.saveAppointments(sampleList);

        // 2. Creiamo una nuova lista con 2 elementi
        List<Appointment> newList = new ArrayList<>();
        newList.add(new Appointment("Meeting A", "Desc A", LocalDateTime.now(), LocalDateTime.now().plusHours(1), "Work"));
        newList.add(new Appointment("Meeting B", "Desc B", LocalDateTime.now(), LocalDateTime.now().plusHours(1), "Work"));

        // 3. Sovrascrittura
        AppointmentPersistence.saveAppointments(newList);

        // 4. Verifica
        List<Appointment> loaded = AppointmentPersistence.loadAppointments();
        assertEquals(2, loaded.size(), "Il file deve contenere solo i nuovi dati");
        assertEquals("Meeting A", loaded.get(0).getTitle());
    }

    // ✅ TEST 4: Lista Vuota
    @Test
    @Order(4)
    @DisplayName("Salvataggio lista vuota")
    void testSave_EmptyList() {
        AppointmentPersistence.saveAppointments(new ArrayList<>());
        
        List<Appointment> loaded = AppointmentPersistence.loadAppointments();
        assertNotNull(loaded);
        assertTrue(loaded.isEmpty());
    }

    // 💣 TEST 5: Robustezza - JSON Corrotto
    @Test
    @Order(5)
    @DisplayName("Robustezza: Comportamento con file JSON corrotto")
    void testLoad_CorruptedJsonFile() throws IOException {
        // Scriviamo spazzatura nel file
        try (FileWriter writer = new FileWriter(FILENAME)) {
            writer.write("{ \"title\": \"Brok... (json non chiuso)");
        }

        // Il comportamento attuale del tuo codice è catturare IOException ma NON JsonSyntaxException.
        // Se non hai modificato AppointmentPersistence, questo test si aspetta un crash (JsonSyntaxException).
        // Se vuoi che il test passi confermando il crash:
        assertThrows(JsonSyntaxException.class, () -> {
            AppointmentPersistence.loadAppointments();
        });
    }
    
    // 🌍 TEST 6: Caratteri Speciali
    @Test
    @Order(6)
    @DisplayName("Supporto caratteri speciali")
    void testSave_SpecialCharacters() {
        Appointment special = new Appointment(
            "Rendez-vous @ & €", 
            "Text with \"quotes\"",
            LocalDateTime.now(),
            LocalDateTime.now().plusHours(1),
            "Spécial"
        );
        
        AppointmentPersistence.saveAppointments(List.of(special));
        
        List<Appointment> loaded = AppointmentPersistence.loadAppointments();
        assertFalse(loaded.isEmpty());
        assertEquals("Rendez-vous @ & €", loaded.get(0).getTitle());
        assertEquals("Spécial", loaded.get(0).getGroup());
    }
}
