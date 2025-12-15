package controllers;

import javafx.application.Platform;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.concurrent.CountDownLatch;

import static org.junit.jupiter.api.Assertions.*;

class EquipementControllerTest {

    private EquipementController controller;
    private VBox categoryListMock;

    // ✅ Démarrage JavaFX UNE FOIS pour tous les tests
    @BeforeAll
    static void initJavaFX() throws InterruptedException {
        CountDownLatch latch = new CountDownLatch(1);
        Platform.startup(latch::countDown);
        latch.await();
    }

    @BeforeEach
    void setUp() throws Exception {
        controller = new EquipementController();
        categoryListMock = new VBox();

        Field field = EquipementController.class.getDeclaredField("categoryList");
        field.setAccessible(true);
        field.set(controller, categoryListMock);
    }

    // ✅ TEST 1
    @Test
    void testAddCategoryAddsItemToList() {
        controller.addCategory("Test Category");
        assertEquals(1, categoryListMock.getChildren().size());
    }

    // ✅ TEST 2
    @Test
    void testAddCategoryContainsCorrectLabelAndButton() {
        controller.addCategory("Radiologie");

        HBox item = (HBox) categoryListMock.getChildren().get(0);
        Label label = (Label) item.getChildren().get(0);
        Button button = (Button) item.getChildren().get(1);

        assertEquals("Radiologie", label.getText());
        assertEquals("Voir les détails", button.getText());
    }
}
