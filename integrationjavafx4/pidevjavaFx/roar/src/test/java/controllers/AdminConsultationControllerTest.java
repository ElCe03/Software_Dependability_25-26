package controllers;

import entite.Consultation;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import service.ConsultationService;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.control.Button;
import javafx.scene.control.ComboBox;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AdminConsultationControllerTest {

    @Mock
    private ConsultationService consultationService;

    // --- MOCK DEI COMPONENTI GRAFICI ---
    // Invece di crearli con 'new', li mokkiamo. 
    // Così non avviano il motore grafico.
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
    void setUp() throws Exception {
        controller = new AdminConsultationController();

        // 1. Iniettiamo i Mock nel controller
        inject(controller, "consultationService", consultationService);
        inject(controller, "consultationTable", consultationTable);
        inject(controller, "searchField", searchField);
        inject(controller, "statusFilterCombo", statusFilterCombo);
        inject(controller, "statsButton", statsButton);
        inject(controller, "pieChartButton", pieChartButton);
        inject(controller, "exportPdfButton", exportPdfButton);
        inject(controller, "mostLikedButton", mostLikedButton);

        // 2. IMPORTANTE: Simuliamo il comportamento delle liste JavaFX
        // Quando il controller chiede table.getItems(), restituiamo una lista vuota sicura.
        lenient().when(consultationTable.getItems()).thenReturn(FXCollections.observableArrayList());
        // Se il controller usa statusFilterCombo.getItems(), scommenta la riga sotto:
        // lenient().when(statusFilterCombo.getItems()).thenReturn(FXCollections.observableArrayList());

        // 3. Setup del service
        lenient().when(consultationService.getAllConsultations()).thenReturn(List.of());
    }

    // --- Metodi di utilità per la reflection (Invariati) ---
    private void inject(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            fail("Failed to inject field: " + fieldName + " due to " + e.getMessage());
        }
    }

    private Object get(String fieldName) {
        try {
            Field f = AdminConsultationController.class.getDeclaredField(fieldName);
            f.setAccessible(true);
            return f.get(controller);
        } catch (Exception e) {
            fail("Failed to get field: " + fieldName + " due to " + e.getMessage());
            return null;
        }
    }

    // --- TEST DI INIEZIONE (Ora verificano i Mock) ---
    @Test
    void testButtonsInjected() {
        assertNotNull(get("statsButton"));
        assertNotNull(get("pieChartButton"));
    }

    @Test
    void testSearchFieldInjected() {
        assertNotNull(get("searchField"));
    }

    // --- PARAMETERIZED TEST ---
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

    // --- BOUNDARY TESTING ---
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

    // --- NEGATIVE TESTING ---
    @Test
    void testStatusMessageNullInput() {
        // Qui non serve reflection complessa per l'assert, Mockito gestisce tutto in modo pulito
        var method = assertDoesNotThrow(() -> AdminConsultationController.class.getDeclaredMethod("getStatusSpecificMessage", String.class));
        method.setAccessible(true);

        InvocationTargetException thrown = assertThrows(InvocationTargetException.class, () -> {
            method.invoke(controller, (String) null);
        });

        assertEquals(NullPointerException.class, thrown.getCause().getClass());
    }

    // --- TEST LOGICO SENZA GRAFICA ---
    @Test
    void testMostLikedServicesEmptyList() throws Exception {
        // Configurazione
        when(consultationService.getAllConsultations()).thenReturn(List.of());

        var method = AdminConsultationController.class.getDeclaredMethod("showMostLikedServices");
        method.setAccessible(true);

        // ESECUZIONE DIRETTA (Niente Platform.runLater!)
        // Poiché i componenti sono Mock, non si lamenteranno di non essere nel thread JavaFX.
        assertDoesNotThrow(() -> method.invoke(controller));

        // Verifica
        verify(consultationService, times(1)).getAllConsultations();
    }
}
