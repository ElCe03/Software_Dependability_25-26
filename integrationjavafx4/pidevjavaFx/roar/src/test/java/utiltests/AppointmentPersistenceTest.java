package util;

import com.google.gson.JsonSyntaxException;
import entite.Appointment;
import org.junit.jupiter.api.*;

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
        deletePersistenceFile();

        sampleList = new ArrayList<>();
        Appointment a1 = new Appointment();
        a1.setId(1);
        a1.setTitle("Consultation Cardiologie");
        a1.setDescription("Suivi patient");
        a1.setStartDateTime(LocalDateTime.of(2025, 10, 10, 14, 30));
        a1.setEndDateTime(LocalDateTime.of(2025, 10, 10, 15, 0));
        
        sampleList.add(a1);
    }

    @AfterEach
    void tearDown() {
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

    @Test
    @Order(1)
    @DisplayName("Salvataggio e ricaricamento: i dati devono corrispondere")
    void testSaveAndLoad_RoundTrip() {
        AppointmentPersistence.saveAppointments(sampleList);

        File file = new File(FILENAME);
        assertTrue(file.exists(), "Il file JSON deve essere creato dopo il salvataggio");
        assertTrue(file.length() > 0, "Il file JSON non deve essere vuoto");

        List<Appointment> loadedList = AppointmentPersistence.loadAppointments();

        assertNotNull(loadedList);
        assertEquals(1, loadedList.size());

        Appointment loaded = loadedList.get(0);
        Appointment original = sampleList.get(0);

        assertEquals(original.getId(), loaded.getId());
        assertEquals(original.getTitle(), loaded.getTitle());
        
        assertEquals(original.getStartDateTime(), loaded.getStartDateTime(), "La data di inizio deve essere preservata correttamente dopo la serializzazione");
    }

    @Test
    @Order(2)
    @DisplayName("Caricamento senza file: deve ritornare lista vuota, non null o crash")
    void testLoad_FileDoesNotExist() {
        deletePersistenceFile();

        List<Appointment> result = AppointmentPersistence.loadAppointments();

        assertNotNull(result, "Il metodo non deve ritornare null se il file manca");
        assertTrue(result.isEmpty(), "Deve ritornare una lista vuota");
    }

    @Test
    @Order(3)
    @DisplayName("Salvataggio successivo: deve sovrascrivere, non appendere")
    void testSave_OverwritesExistingData() {
        AppointmentPersistence.saveAppointments(sampleList);

        List<Appointment> newList = new ArrayList<>();
        newList.add(new Appointment());
        newList.add(new Appointment());

        AppointmentPersistence.saveAppointments(newList);

        List<Appointment> loaded = AppointmentPersistence.loadAppointments();

        assertEquals(2, loaded.size(), "Il file deve contenere solo l'ultimo set di dati");
    }

    @Test
    @Order(4)
    @DisplayName("Salvataggio lista vuota")
    void testSave_EmptyList() {
        AppointmentPersistence.saveAppointments(new ArrayList<>());
        
        List<Appointment> loaded = AppointmentPersistence.loadAppointments();
        assertNotNull(loaded);
        assertTrue(loaded.isEmpty());
    }

    
    @Test
    @Order(5)
    @DisplayName("Supporto caratteri speciali e Unicode")
    void testSave_SpecialCharacters() {
        Appointment special = new Appointment();
        special.setTitle("Rendez-vous @ & € £ §");
        special.setDescription("Text with \n newline and \"quotes\"");
        
        AppointmentPersistence.saveAppointments(List.of(special));
        
        List<Appointment> loaded = AppointmentPersistence.loadAppointments();
        assertEquals("Rendez-vous @ & € £ §", loaded.get(0).getTitle());
        assertEquals("Text with \n newline and \"quotes\"", loaded.get(0).getDescription());
    }
}