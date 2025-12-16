package controllers;

import entite.Consultation;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable; 
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.mockito.junit.jupiter.MockitoSettings;
import org.mockito.quality.Strictness;
import service.ConsultationService;

import javafx.collections.FXCollections;
import javafx.scene.control.Button;
import javafx.scene.control.ComboBox;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;

import java.lang.reflect.Field;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisabledIfEnvironmentVariable(named = "CI", matches = "true")
class AdminConsultationControllerTest {

    @Mock
    private ConsultationService consultationService;
    @Mock
    private TableView<Consultation> consultationTable;
    @Mock
    private TextField searchField;
    @Mock
    private ComboBox<String> statusFilterCombo;
    @Mock
    private Button statsButton;
    @Mock
    private Button pieChartButton;
    @Mock
    private Button exportPdfButton;
    @Mock
    private Button mostLikedButton;

    private AdminConsultationController controller;

    @BeforeEach
    void setUp() {
        try {
            controller = new AdminConsultationController();
            inject(controller, "consultationService", consultationService);
            inject(controller, "consultationTable", consultationTable);
            inject(controller, "searchField", searchField);
            inject(controller, "statusFilterCombo", statusFilterCombo);
            inject(controller, "statsButton", statsButton);
            inject(controller, "pieChartButton", pieChartButton);
            inject(controller, "exportPdfButton", exportPdfButton);
            inject(controller, "mostLikedButton", mostLikedButton);

            lenient().when(consultationTable.getItems()).thenReturn(FXCollections.observableArrayList());
            lenient().when(consultationService.getAllConsultations()).thenReturn(List.of());
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
    }

    @Test
    void testButtonsInjected() {
        assertNotNull(get("statsButton"));
        assertNotNull(get("pieChartButton"));
    }

    @Test
    void testSearchFieldInjected() {
        assertNotNull(get("searchField"));
    }

    @ParameterizedTest
    @CsvSource({
            "Confirmed, confirm",
            "Done, experience",
            "En cours de traitement, process",
            "UNKNOWN, ''"
    })
    void testStatusSpecificMessage(String input, String expectedContent) throws Exception {
        var method = AdminConsultationController.class.getDeclaredMethod("getStatusSpecificMessage", String.class);
        method.setAccessible(true);
        String result = (String) method.invoke(controller, input);

        if (expectedContent.isEmpty()) {
            assertEquals("", result);
        } else {
            assertTrue(result.toLowerCase().contains(expectedContent));
        }
    }

    @Test
    void testRatingStorageBoundaries() throws Exception {
        var saveMethod = AdminConsultationController.class.getDeclaredMethod("saveRatingForConsultation", int.class, int.class);
        saveMethod.setAccessible(true);
        var getMethod = AdminConsultationController.class.getDeclaredMethod("getRatingForConsultation", int.class);
        getMethod.setAccessible(true);

        int[] ratings = {0, 1, 3, 5, 10};
        for (int r : ratings) {
            saveMethod.invoke(controller, 200, r);
            int result = (int) getMethod.invoke(controller, 200);
            assertEquals(r, result);
        }
    }

    @Test
    void testMostLikedServicesEmptyList() throws Exception {
        var method = AdminConsultationController.class.getDeclaredMethod("showMostLikedServices");
        method.setAccessible(true);

        assertDoesNotThrow(() -> method.invoke(controller));
        verify(consultationService, times(1)).getAllConsultations();
    }

    private void inject(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            fail("Failed to inject field: " + fieldName);
        }
    }

    private Object get(String fieldName) {
        try {
            Field f = AdminConsultationController.class.getDeclaredField(fieldName);
            f.setAccessible(true);
            return f.get(controller);
        } catch (Exception e) {
            return null;
        }
    }
}
