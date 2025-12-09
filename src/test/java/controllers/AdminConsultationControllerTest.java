package controllers;

import javafx.scene.control.*;
import org.junit.jupiter.api.*;
import utils.JavaFXTestUtils;

import java.lang.reflect.Field;
import static org.junit.jupiter.api.Assertions.*;

class AdminConsultationControllerTest {

    private AdminConsultationController controller;

    @BeforeAll
    static void beforeAll() {
        JavaFXTestUtils.initJavaFX();
    }

    @BeforeEach
    void setUp() throws Exception {
        controller = new AdminConsultationController();

        JavaFXTestUtils.runAndWait(() -> {
            inject("consultationTable", new TableView<>());
            inject("searchField", new TextField());
            inject("statusFilterCombo", new ComboBox<>());
            inject("statsButton", new Button());
            inject("pieChartButton", new Button());
            inject("exportPdfButton", new Button());
            inject("mostLikedButton", new Button());
            controller.initialize();
        });
    }

    private void inject(String fieldName, Object value) {
        try {
            Field f = AdminConsultationController.class.getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(controller, value);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private Object get(String fieldName) {
        try {
            Field f = AdminConsultationController.class.getDeclaredField(fieldName);
            f.setAccessible(true);
            return f.get(controller);
        } catch (Exception e) {
            throw new RuntimeException(e);
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
}
