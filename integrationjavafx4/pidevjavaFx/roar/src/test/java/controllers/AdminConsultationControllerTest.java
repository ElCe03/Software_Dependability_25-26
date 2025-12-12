package controllers;

import entite.Consultation;
import javafx.scene.control.*;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import service.ConsultationService;
import utils.JavaFXTestUtils;

import java.lang.reflect.Field;
import java.sql.Date;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AdminConsultationControllerTest {

    // 1. Create the Mock
    @Mock
    private ConsultationService consultationService;

    // We instantiate the controller manually to ensure full control over its lifecycle
    private AdminConsultationController controller;

    @BeforeAll
    static void beforeAll() {
        JavaFXTestUtils.initJavaFX();
    }

    @BeforeEach
    void setUp() throws Exception {
        controller = new AdminConsultationController();

        // 2. Initialize JavaFX components and the Controller
        JavaFXTestUtils.runAndWait(() -> {
            inject(controller, "consultationTable", new TableView<>());
            inject(controller, "searchField", new TextField());
            inject(controller, "statusFilterCombo", new ComboBox<>());
            inject(controller, "statsButton", new Button());
            inject(controller, "pieChartButton", new Button());
            inject(controller, "exportPdfButton", new Button());
            inject(controller, "mostLikedButton", new Button());

            // This method likely overwrites 'consultationService' with a real instance
            controller.initialize();
        });

        // 3. CRITICAL FIX: Inject the Mock Service AFTER initialize()
        // This ensures the controller uses OUR mock, not the one it created internally.
        inject(controller, "consultationService", consultationService);
    }

    /** * Reflection helper to inject private fields into the controller.
     */
    private void inject(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to inject field: " + fieldName, e);
        }
    }

    /** * Reflection helper to get private fields from the controller.
     */
    private Object get(String fieldName) {
        try {
            Field f = AdminConsultationController.class.getDeclaredField(fieldName);
            f.setAccessible(true);
            return f.get(controller);
        } catch (Exception e) {
            throw new RuntimeException("Failed to get field: " + fieldName, e);
        }
    }

    @Test
    void testButtonsInjected() {
        assertNotNull(get("statsButton"));
        assertNotNull(get("pieChartButton"));
        assertNotNull(get("exportPdfButton"));
        assertNotNull(get("mostLikedButton"));
    }

    @Test
    void testComboAndTableInjected() {
        assertNotNull(get("statusFilterCombo"));
        assertNotNull(get("consultationTable"));
    }

    @Test
    void testSearchFieldInjected() {
        assertNotNull(get("searchField"));
    }

    @Test
    void testStatusMessagesCoverage() throws Exception {
        var method = AdminConsultationController.class
                .getDeclaredMethod("getStatusSpecificMessage", String.class);
        method.setAccessible(true);

        assertTrue(((String) method.invoke(controller, "Confirmed")).toLowerCase().contains("confirm"));
        assertTrue(((String) method.invoke(controller, "Done")).toLowerCase().contains("experience"));
        assertTrue(((String) method.invoke(controller, "En cours de traitement")).toLowerCase().contains("process"));
        assertEquals("", method.invoke(controller, "UNKNOWN"));
    }

    @Test
    void testRatingStorage() throws Exception {
        var saveMethod = AdminConsultationController.class
                .getDeclaredMethod("saveRatingForConsultation", int.class, int.class);
        saveMethod.setAccessible(true);

        var getMethod = AdminConsultationController.class
                .getDeclaredMethod("getRatingForConsultation", int.class);
        getMethod.setAccessible(true);

        saveMethod.invoke(controller, 101, 4);
        int rating = (int) getMethod.invoke(controller, 101);
        assertEquals(4, rating);

        saveMethod.invoke(controller, 101, 5);
        rating = (int) getMethod.invoke(controller, 101);
        assertEquals(5, rating);
    }

    @Test
    void testMostLikedServicesLogic_Success() throws Exception {
        // 1. Prepare Data
        Consultation c1 = new Consultation();
        c1.setId(1);
        c1.setServiceName("Service A");
        c1.setDate(new Date(System.currentTimeMillis()));
        c1.setStatus("Done");

        Consultation c2 = new Consultation();
        c2.setId(2);
        c2.setServiceName("Service B");
        c2.setDate(new Date(System.currentTimeMillis()));
        c2.setStatus("Confirmed");

        List<Consultation> consultations = List.of(c1, c2);

        // 2. Configure Mock
        // If the controller calls this method, it MUST return our list
        when(consultationService.getAllConsultations()).thenReturn(consultations);

        // 3. Save Ratings (Setup State)
        var saveMethod = AdminConsultationController.class
                .getDeclaredMethod("saveRatingForConsultation", int.class, int.class);
        saveMethod.setAccessible(true);
        saveMethod.invoke(controller, 1, 5);
        saveMethod.invoke(controller, 2, 3);

        // 4. Invoke Method Under Test (on FX Thread)
        var mostLikedMethod = AdminConsultationController.class
                .getDeclaredMethod("showMostLikedServices");
        mostLikedMethod.setAccessible(true);

        JavaFXTestUtils.runAndWait(() -> {
            assertDoesNotThrow(() -> mostLikedMethod.invoke(controller));
        });

        // 5. Verify Interaction
        verify(consultationService, times(1)).getAllConsultations();
    }
}