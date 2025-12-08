package controllers;

import entite.departement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.List;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import static org.junit.jupiter.api.Assertions.*;

class DepartementControllerTest {

    private DepartementController controller;

    @BeforeEach
    void setUp() {
        controller = new DepartementController();
    }

    // ✅ TEST 1 — Création du dossier des images
    @Test
    void testCreateImageDirectory() throws Exception {
        Method method = DepartementController.class.getDeclaredMethod("createImageDirectory");
        method.setAccessible(true);
        method.invoke(controller);

        File dir = new File(DepartementController.IMAGE_DIR);
        assertTrue(dir.exists());
        assertTrue(dir.isDirectory());
    }

    // ✅ TEST 2 — Filtrage des départements par nom
    @Test
    void testFilterDepartementsByNom() throws Exception {

        ObservableList<departement> departementData = FXCollections.observableArrayList();
        ObservableList<departement> filteredData = FXCollections.observableArrayList();

        departement d1 = new departement();
        d1.setNom("Cardiologie");
        d1.setAdresse("Tunis");

        departement d2 = new departement();
        d2.setNom("Pédiatrie");
        d2.setAdresse("Sfax");

        departementData.addAll(d1, d2);
        filteredData.setAll(departementData);

        Field dataField = DepartementController.class.getDeclaredField("departementData");
        Field filteredField = DepartementController.class.getDeclaredField("filteredDepartementData");

        dataField.setAccessible(true);
        filteredField.setAccessible(true);

        dataField.set(controller, departementData);
        filteredField.set(controller, filteredData);

        Method method = DepartementController.class.getDeclaredMethod("filterDepartements", String.class);
        method.setAccessible(true);
        method.invoke(controller, "card");

        ObservableList<departement> result =
                (ObservableList<departement>) filteredField.get(controller);

        assertEquals(1, result.size());
        assertEquals("Cardiologie", result.get(0).getNom());
    }

    // ✅ TEST 3 — Filtrage des départements par adresse
    @Test
    void testFilterDepartementsByAdresse() throws Exception {

        ObservableList<departement> departementData = FXCollections.observableArrayList();
        ObservableList<departement> filteredData = FXCollections.observableArrayList();

        departement d1 = new departement();
        d1.setNom("Urgence");
        d1.setAdresse("Tunis");

        departement d2 = new departement();
        d2.setNom("Radio");
        d2.setAdresse("Sousse");

        departementData.addAll(d1, d2);
        filteredData.setAll(departementData);

        Field dataField = DepartementController.class.getDeclaredField("departementData");
        Field filteredField = DepartementController.class.getDeclaredField("filteredDepartementData");

        dataField.setAccessible(true);
        filteredField.setAccessible(true);

        dataField.set(controller, departementData);
        filteredField.set(controller, filteredData);

        Method method = DepartementController.class.getDeclaredMethod("filterDepartements", String.class);
        method.setAccessible(true);
        method.invoke(controller, "sousse");

        ObservableList<departement> result =
                (ObservableList<departement>) filteredField.get(controller);

        assertEquals(1, result.size());
        assertEquals("Sousse", result.get(0).getAdresse());
    }

    // ✅ TEST 4 — Filtre vide = retourne tout
    @Test
    void testFilterDepartementsEmpty() throws Exception {

        ObservableList<departement> departementData = FXCollections.observableArrayList();
        ObservableList<departement> filteredData = FXCollections.observableArrayList();

        departement d1 = new departement();
        d1.setNom("A");

        departement d2 = new departement();
        d2.setNom("B");

        departementData.addAll(d1, d2);
        filteredData.setAll(departementData);

        Field dataField = DepartementController.class.getDeclaredField("departementData");
        Field filteredField = DepartementController.class.getDeclaredField("filteredDepartementData");

        dataField.setAccessible(true);
        filteredField.setAccessible(true);

        dataField.set(controller, departementData);
        filteredField.set(controller, filteredData);

        Method method = DepartementController.class.getDeclaredMethod("filterDepartements", String.class);
        method.setAccessible(true);
        method.invoke(controller, "");

        ObservableList<departement> result =
                (ObservableList<departement>) filteredField.get(controller);

        assertEquals(2, result.size());
    }
}
