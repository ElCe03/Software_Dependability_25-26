package controllers;

import javafx.application.Platform;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Assumptions;

import java.lang.reflect.Field;
import java.util.concurrent.CountDownLatch;

import static org.junit.jupiter.api.Assertions.*;

class EquipementControllerTest {

    private EquipementController controller;
    private VBox categoryListMock;

    private static boolean isHeadlessCI() {
        return System.getenv("CI") != null || java.awt.GraphicsEnvironment.isHeadless();
    }

    @BeforeAll
    static void initJavaFX() throws InterruptedException {
        if (isHeadlessCI()) {
            return;
        }

        try {
            CountDownLatch latch = new CountDownLatch(1);
            Platform.startup(latch::countDown);
            latch.await();
        } catch (IllegalStateException e) {
            
        }
    }

    @BeforeEach
    void setUp() throws Exception {
        if (isHeadlessCI()) return;

        controller = new EquipementController();
        categoryListMock = new VBox();

        Field field = EquipementController.class.getDeclaredField("categoryList");
        field.setAccessible(true);
        field.set(controller, categoryListMock);
    }

    @Test
    void testAddCategoryAddsItemToList() {
        Assumptions.assumeFalse(isHeadlessCI());

        controller.addCategory("Test Category");
        assertEquals(1, categoryListMock.getChildren().size());
    }

    @Test
    void testAddCategoryContainsCorrectLabelAndButton() {
        Assumptions.assumeFalse(isHeadlessCI());

        controller.addCategory("Radiologie");

        HBox item = (HBox) categoryListMock.getChildren().get(0);
        Label label = (Label) item.getChildren().get(0);
        Button button = (Button) item.getChildren().get(1);

        assertEquals("Radiologie", label.getText());
        assertEquals("Voir les détails", button.getText());
    }
}
