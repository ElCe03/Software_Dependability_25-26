package controllers;

import entite.Service;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.collections.transformation.SortedList;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.layout.GridPane;
import service.serviceservice;

import java.util.List;
import java.util.Optional;

public class MedicalServicesController {

    private final serviceservice serviceService = new serviceservice();
    private final ObservableList<Service> servicesData = FXCollections.observableArrayList();
    private FilteredList<Service> filteredServices;
    private SortedList<Service> sortedServices;

    // FXML Components
    @FXML private TextField serviceName;
    @FXML private TextArea serviceDescription;
    @FXML private Spinner<Integer> durationSpinner;
    @FXML private TableView<Service> servicesTable;
    @FXML private TableColumn<Service, String> nameColumn;
    @FXML private TableColumn<Service, String> descriptionColumn;
    @FXML private TableColumn<Service, Integer> durationColumn;
    @FXML private TableColumn<Service, Void> modifyColumn;
    @FXML private TableColumn<Service, Void> deleteColumn;
    @FXML private TextField searchField;
    @FXML private Button submitButton; // Added for the styled button

    // Error Labels
    @FXML private Label serviceNameError;
    @FXML private Label serviceDescriptionError;
    @FXML private Label durationError;

    @FXML
    private void handleSubmit() {
        clearErrorMessages();

        try {
            String name = serviceName.getText().trim();
            String description = serviceDescription.getText().trim();
            int duration = durationSpinner.getValue();

            if (!validateInputs(name, description, duration)) {
                return;
            }

            Service newService = new Service(name, description, duration);
            serviceService.addService(newService);
            refreshTableData();
            clearForm();
            showAlert("Success", "Service added successfully!", Alert.AlertType.INFORMATION);

        } catch (Exception e) {
            showAlert("Database Error", "Failed to add service: " + e.getMessage(), Alert.AlertType.ERROR);
            e.printStackTrace();
        }
    }

    private boolean validateInputs(String name, String description, int duration) {
        boolean valid = true;

        if (name.isEmpty()) {
            serviceNameError.setText("Service name cannot be blank!");
            valid = false;
        } else if (name.length() < 3) {
            serviceNameError.setText("Service name must be at least 3 characters long!");
            valid = false;
        } else if (name.matches(".*\\d.*")) {
            serviceNameError.setText("Service name cannot contain numbers!");
            valid = false;
        }

        if (description.isEmpty()) {
            serviceDescriptionError.setText("Description cannot be blank!");
            valid = false;
        } else if (!description.contains(" ")) {
            serviceDescriptionError.setText("Description must contain at least one space!");
            valid = false;
        }

        if (duration <= 0) {
            durationError.setText("Duration must be greater than 0!");
            valid = false;
        }

        return valid;
    }

    private void clearErrorMessages() {
        serviceNameError.setText("");
        serviceDescriptionError.setText("");
        durationError.setText("");
    }

    private void refreshTableData() {
        try {
            List<Service> services = serviceService.getAllServices();
            servicesData.setAll(services);
            servicesTable.refresh();
        } catch (Exception e) {
            showAlert("Error", "Failed to load services: " + e.getMessage(), Alert.AlertType.ERROR);
            e.printStackTrace();
        }
    }

    private void clearForm() {
        serviceName.clear();
        serviceDescription.clear();
        durationSpinner.getValueFactory().setValue(1);
    }

    private void showAlert(String title, String message, Alert.AlertType alertType) {
        Alert alert = new Alert(alertType);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    @FXML
    private void initialize() {
        setupFormControls();
        setupTableColumns();
        setupSearchFunctionality();
        setupTableButtons();
        styleSubmitButton(); // Style the existing button
        refreshTableData();
    }

    private void setupFormControls() {
        durationSpinner.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 1000, 1));
    }

    private void setupTableColumns() {
        nameColumn.setCellValueFactory(new PropertyValueFactory<>("name"));
        descriptionColumn.setCellValueFactory(new PropertyValueFactory<>("description"));
        durationColumn.setCellValueFactory(new PropertyValueFactory<>("duration"));
        servicesTable.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY);
    }

    private void setupSearchFunctionality() {
        filteredServices = new FilteredList<>(servicesData, p -> true);
        sortedServices = new SortedList<>(filteredServices);
        sortedServices.comparatorProperty().bind(servicesTable.comparatorProperty());

        searchField.textProperty().addListener((observable, oldValue, newValue) -> {
            Platform.runLater(() -> updateSearchFilter(newValue));
        });

        servicesTable.setItems(sortedServices);
    }

    private void updateSearchFilter(String searchText) {
        filteredServices.setPredicate(service -> {
            if (searchText == null || searchText.isEmpty()) {
                return true;
            }
            String lowerCaseFilter = searchText.toLowerCase();
            return service.getName().toLowerCase().contains(lowerCaseFilter) ||
                    service.getDescription().toLowerCase().contains(lowerCaseFilter);
        });
    }

    private void setupTableButtons() {
        addModifyButtonToTable();
        addDeleteButtonToTable();
    }

    private void addModifyButtonToTable() {
        modifyColumn.setCellFactory(param -> new TableCell<>() {
            private final Button modifyButton = new Button("Modify");

            {
                modifyButton.setStyle("-fx-background-color: #2196F3; -fx-text-fill: white;");
                modifyButton.setOnAction(event -> {
                    Service service = getTableView().getItems().get(getIndex());
                    handleModify(service);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : modifyButton);
            }
        });
    }

    private void addDeleteButtonToTable() {
        deleteColumn.setCellFactory(param -> new TableCell<>() {
            private final Button deleteButton = new Button("Delete");

            {
                deleteButton.setStyle("-fx-background-color: #F44336; -fx-text-fill: white;");
                deleteButton.setOnAction(event -> {
                    Service service = getTableView().getItems().get(getIndex());
                    handleDelete(service);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                setGraphic(empty ? null : deleteButton);
            }
        });
    }

    private void styleSubmitButton() {
        if (submitButton != null) {
            // Red-to-blue gradient effect
            submitButton.setStyle(
                    "-fx-background-color: linear-gradient(to right, #FF5252, #2196F3);" +
                            "-fx-text-fill: white;" +
                            "-fx-font-weight: bold;" +
                            "-fx-background-radius: 5px;"
            );

            // Hover effect - darker version of the gradient
            submitButton.setOnMouseEntered(e -> submitButton.setStyle(
                    "-fx-background-color: linear-gradient(to right, #FF1744, #1976D2);" +
                            "-fx-text-fill: white;" +
                            "-fx-font-weight: bold;" +
                            "-fx-background-radius: 5px;" +
                            "-fx-effect: dropshadow(three-pass-box, rgba(0,0,0,0.3), 5, 0, 0, 1);"
            ));

            // Normal state when mouse exits
            submitButton.setOnMouseExited(e -> submitButton.setStyle(
                    "-fx-background-color: linear-gradient(to right, #FF5252, #2196F3);" +
                            "-fx-text-fill: white;" +
                            "-fx-font-weight: bold;" +
                            "-fx-background-radius: 5px;" +
                            "-fx-effect: null;"
            ));

            // Pressed effect
            submitButton.setOnMousePressed(e -> submitButton.setStyle(
                    "-fx-background-color: linear-gradient(to right, #D50000, #0D47A1);" +
                            "-fx-text-fill: white;" +
                            "-fx-font-weight: bold;" +
                            "-fx-background-radius: 5px;" +
                            "-fx-effect: innershadow(three-pass-box, rgba(0,0,0,0.4), 2, 0, 0, 0);"
            ));
        }
    }

    private void handleModify(Service service) {
        Dialog<Service> dialog = createModifyDialog(service);
        Optional<Service> result = dialog.showAndWait();

        if (result.isPresent()) {
            try {
                Service updatedService = result.get();
                if (validateInputs(updatedService.getName(), updatedService.getDescription(), updatedService.getDuration())) {
                    serviceService.updateService(updatedService);
                    refreshTableData();
                    showAlert("Success", "Service updated successfully!", Alert.AlertType.INFORMATION);
                }
            } catch (Exception e) {
                showAlert("Error", "Failed to update service: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
    }

    private Dialog<Service> createModifyDialog(Service service) {
        Dialog<Service> dialog = new Dialog<>();
        dialog.setTitle("Modify Service");
        dialog.setHeaderText("Edit Service Details");

        TextField nameField = new TextField(service.getName());
        TextArea descriptionField = new TextArea(service.getDescription());
        Spinner<Integer> durationSpinner = new Spinner<>(1, 1000, service.getDuration());

        Label nameError = new Label();
        Label descriptionError = new Label();
        Label durationError = new Label();

        nameError.setStyle("-fx-text-fill: red;");
        descriptionError.setStyle("-fx-text-fill: red;");
        durationError.setStyle("-fx-text-fill: red;");

        GridPane grid = new GridPane();
        grid.setHgap(10);
        grid.setVgap(10);
        grid.add(new Label("Name:"), 0, 0);
        grid.add(nameField, 1, 0);
        grid.add(nameError, 2, 0);
        grid.add(new Label("Description:"), 0, 1);
        grid.add(descriptionField, 1, 1);
        grid.add(descriptionError, 2, 1);
        grid.add(new Label("Duration (minutes):"), 0, 2);
        grid.add(durationSpinner, 1, 2);
        grid.add(durationError, 2, 2);

        dialog.getDialogPane().setContent(grid);
        dialog.getDialogPane().getButtonTypes().addAll(ButtonType.OK, ButtonType.CANCEL);

        Node okButton = dialog.getDialogPane().lookupButton(ButtonType.OK);
        okButton.setDisable(false);

        nameField.textProperty().addListener((obs, oldVal, newVal) -> validateDialogFields(nameField, nameError, descriptionField, descriptionError, durationSpinner, durationError, okButton));
        descriptionField.textProperty().addListener((obs, oldVal, newVal) -> validateDialogFields(nameField, nameError, descriptionField, descriptionError, durationSpinner, durationError, okButton));
        durationSpinner.valueProperty().addListener((obs, oldVal, newVal) -> validateDialogFields(nameField, nameError, descriptionField, descriptionError, durationSpinner, durationError, okButton));

        dialog.setResultConverter(buttonType -> {
            if (buttonType == ButtonType.OK) {
                service.setName(nameField.getText().trim());
                service.setDescription(descriptionField.getText().trim());
                service.setDuration(durationSpinner.getValue());
                return service;
            }
            return null;
        });

        return dialog;
    }

    private void validateDialogFields(TextField nameField, Label nameError,
                                      TextArea descriptionField, Label descriptionError,
                                      Spinner<Integer> durationSpinner, Label durationError,
                                      Node okButton) {
        boolean valid = true;

        String name = nameField.getText().trim();
        if (name.isEmpty()) {
            nameError.setText("Service name cannot be blank!");
            valid = false;
        } else if (name.length() < 3) {
            nameError.setText("Service name must be at least 3 characters long!");
            valid = false;
        } else if (name.matches(".*\\d.*")) {
            nameError.setText("Service name cannot contain numbers!");
            valid = false;
        } else {
            nameError.setText("");
        }

        String description = descriptionField.getText().trim();
        if (description.isEmpty()) {
            descriptionError.setText("Description cannot be blank!");
            valid = false;
        } else if (!description.contains(" ")) {
            descriptionError.setText("Description must contain at least one space!");
            valid = false;
        } else {
            descriptionError.setText("");
        }

        int duration = durationSpinner.getValue();
        if (duration <= 0) {
            durationError.setText("Duration must be greater than 0!");
            valid = false;
        } else {
            durationError.setText("");
        }

        okButton.setDisable(!valid);
    }

    private void handleDelete(Service service) {
        Alert confirmation = new Alert(Alert.AlertType.CONFIRMATION);
        confirmation.setTitle("Delete Confirmation");
        confirmation.setHeaderText("Are you sure you want to delete this service?");
        confirmation.setContentText("Service: " + service.getName());

        Optional<ButtonType> result = confirmation.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            try {
                serviceService.deleteService(service.getId());
                refreshTableData();
                showAlert("Success", "Service deleted successfully!", Alert.AlertType.INFORMATION);
            } catch (Exception e) {
                showAlert("Error", "Failed to delete service: " + e.getMessage(), Alert.AlertType.ERROR);
            }
        }
    }

}