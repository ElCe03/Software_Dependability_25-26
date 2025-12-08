package controllers;

import javafx.application.Platform;
import javafx.scene.control.*;
import org.junit.jupiter.api.*;

import java.lang.reflect.Field;

import static org.junit.jupiter.api.Assertions.*;

class AdminConsultationControllerTest {

    private AdminConsultationController controller;

    @BeforeEach
    void setUp() throws Exception {
        controller = new AdminConsultationController();

        // Injection manuelle des composants FXML
        inject("consultationTable", new TableView<>());
        inject("searchField", new TextField());
        inject("statusFilterCombo", new ComboBox<>());
        inject("statsButton", new Button());
        inject("pieChartButton", new Button());
        inject("exportPdfButton", new Button());
        inject("mostLikedButton", new Button());

        // Exécuter initialize sur le thread JavaFX
        Platform.runLater(controller::initialize);

        // Petite pause pour s'assurer que initialize() est exécuté
        Thread.sleep(300);
    }

    private void inject(String fieldName, Object value) throws Exception {
        Field field = AdminConsultationController.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(controller, value);
    }

    private Object getField(String fieldName) throws Exception {
        Field field = AdminConsultationController.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        return field.get(controller);
    }

    @Test
    void testButtonsInjected() throws Exception {
        assertNotNull(getField("statsButton"));
        assertNotNull(getField("pieChartButton"));
        assertNotNull(getField("exportPdfButton"));
        assertNotNull(getField("mostLikedButton"));
    }

    @Test
    void testComboAndTableInjected() throws Exception {
        assertNotNull(getField("statusFilterCombo"));
        assertNotNull(getField("consultationTable"));
    }

    @Test
    void testSearchFieldInjected() throws Exception {
        assertNotNull(getField("searchField"));
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
