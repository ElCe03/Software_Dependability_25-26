package controllers;

import entite.Appointment;
import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Modality;
import javafx.stage.Stage;
import util.AppointmentPersistence;

import java.net.URL;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.YearMonth;
import java.time.format.DateTimeFormatter;
import java.time.format.TextStyle;
import java.util.*;

public class MedicalCalendarController implements Initializable {

    @FXML
    private VBox calendarContainer;

    private ObservableList<Appointment> appointments;
    private List<String> appointmentGroups;
    private YearMonth currentYearMonth;
    private GridPane calendarGrid;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        setupCalendar();
    }

    private void setupCalendar() {
        appointments = FXCollections.observableArrayList();
        appointmentGroups = Arrays.asList("Hospitalisation", "Consultation", "Urgence", "Chirurgie", "Observation");
        currentYearMonth = YearMonth.now();

        VBox mainContainer = new VBox(10);
        mainContainer.setPadding(new Insets(10));
        mainContainer.setStyle("-fx-background-color: #f5f5f5;");

        HBox navigationBar = new HBox(10);
        navigationBar.setAlignment(javafx.geometry.Pos.CENTER);
        navigationBar.setStyle("-fx-background-color: white; -fx-padding: 10; -fx-background-radius: 5;");

        Button prevYearButton = new Button("<<");
        Button prevMonthButton = new Button("<");
        Label monthYearLabel = new Label();
        Button nextMonthButton = new Button(">");
        Button nextYearButton = new Button(">>");

        String navButtonStyle = "-fx-background-color: #2196F3; -fx-text-fill: white; -fx-font-size: 14px; " +
                              "-fx-min-width: 40px; -fx-min-height: 40px; -fx-padding: 5px; " +
                              "-fx-background-radius: 5px; -fx-cursor: hand;";
        prevYearButton.setStyle(navButtonStyle);
        prevMonthButton.setStyle(navButtonStyle);
        nextMonthButton.setStyle(navButtonStyle);
        nextYearButton.setStyle(navButtonStyle);

        monthYearLabel.setStyle("-fx-font-size: 20px; -fx-font-weight: bold; -fx-text-fill: #333333;");

        updateMonthYearLabel(monthYearLabel);

        prevYearButton.setOnAction(e -> {
            currentYearMonth = currentYearMonth.minusYears(1);
            updateMonthYearLabel(monthYearLabel);
            updateCalendar();
        });

        prevMonthButton.setOnAction(e -> {
            currentYearMonth = currentYearMonth.minusMonths(1);
            updateMonthYearLabel(monthYearLabel);
            updateCalendar();
        });

        nextMonthButton.setOnAction(e -> {
            currentYearMonth = currentYearMonth.plusMonths(1);
            updateMonthYearLabel(monthYearLabel);
            updateCalendar();
        });

        nextYearButton.setOnAction(e -> {
            currentYearMonth = currentYearMonth.plusYears(1);
            updateMonthYearLabel(monthYearLabel);
            updateCalendar();
        });

        navigationBar.getChildren().addAll(prevYearButton, prevMonthButton, monthYearLabel, nextMonthButton, nextYearButton);

        calendarGrid = new GridPane();
        calendarGrid.setHgap(5);
        calendarGrid.setVgap(5);
        calendarGrid.setPadding(new Insets(5));
        calendarGrid.setStyle("-fx-background-color: white; -fx-background-radius: 5; -fx-padding: 5;");

        for (int i = 0; i < 7; i++) {
            ColumnConstraints column = new ColumnConstraints();
            column.setHgrow(Priority.ALWAYS);
            column.setFillWidth(true);
            calendarGrid.getColumnConstraints().add(column);
        }

        HBox buttonBox = new HBox(10);
        buttonBox.setPadding(new Insets(10));
        buttonBox.setAlignment(javafx.geometry.Pos.CENTER);
        buttonBox.setStyle("-fx-background-color: white; -fx-background-radius: 5;");
        
        Button addButton = new Button("Ajouter un rendez-vous");
        Button listButton = new Button("Liste des rendez-vous");
        
        String actionButtonStyle = "-fx-background-color: #2196F3; -fx-text-fill: white; -fx-font-size: 14px; " +
                                 "-fx-padding: 8px 15px; -fx-background-radius: 5px; -fx-cursor: hand;";
        addButton.setStyle(actionButtonStyle);
        listButton.setStyle(actionButtonStyle);
        
        addButton.setOnAction(e -> showAddAppointmentDialog());
        listButton.setOnAction(e -> showAppointmentList());
        
        buttonBox.getChildren().addAll(addButton, listButton);

        mainContainer.getChildren().addAll(navigationBar, calendarGrid, buttonBox);

        calendarContainer.getChildren().clear();
        calendarContainer.getChildren().add(mainContainer);

        loadSavedAppointments();
        updateCalendar();
    }

    private void updateMonthYearLabel(Label label) {
        String month = currentYearMonth.getMonth().getDisplayName(TextStyle.FULL, Locale.FRENCH);
        int year = currentYearMonth.getYear();
        label.setText(month + " " + year);
    }

    private void updateCalendar() {
        calendarGrid.getChildren().clear();

        String[] days = {"Lun", "Mar", "Mer", "Jeu", "Ven", "Sam", "Dim"};
        for (int i = 0; i < days.length; i++) {
            Label dayLabel = new Label(days[i]);
            dayLabel.setStyle("-fx-font-weight: bold; -fx-font-size: 12px; -fx-background-color: #e3f2fd; " +
                            "-fx-padding: 5px; -fx-alignment: center; -fx-background-radius: 3px;");
            dayLabel.setMaxWidth(Double.MAX_VALUE);
            dayLabel.setAlignment(javafx.geometry.Pos.CENTER);
            calendarGrid.add(dayLabel, i, 0);
        }

        LocalDate firstOfMonth = currentYearMonth.atDay(1);
        int dayOfWeek = firstOfMonth.getDayOfWeek().getValue();
        int daysInMonth = currentYearMonth.lengthOfMonth();
        int weeks = (int) Math.ceil((dayOfWeek + daysInMonth) / 7.0);

        int day = 1;
        for (int week = 1; week <= weeks; week++) {
            for (int dayOfWeekIndex = 1; dayOfWeekIndex <= 7; dayOfWeekIndex++) {
                if ((week == 1 && dayOfWeekIndex < dayOfWeek) || day > daysInMonth) {
                    Pane emptyCell = new Pane();
                    emptyCell.setStyle("-fx-border-color: #e0e0e0; -fx-border-width: 1; -fx-background-color: #fafafa;");
                    emptyCell.setMinSize(120, 50);
                    calendarGrid.add(emptyCell, dayOfWeekIndex - 1, week);
                } else {
                    VBox dayCell = new VBox(2);
                    dayCell.setStyle("-fx-border-color: #e0e0e0; -fx-border-width: 1; -fx-padding: 2px; " +
                                   "-fx-background-color: white;");
                    dayCell.setMinSize(120, 50);

                    Label dayNumber = new Label(String.valueOf(day));
                    dayNumber.setStyle("-fx-font-weight: bold; -fx-font-size: 12px; -fx-padding: 2px;");
                    dayNumber.setMaxWidth(Double.MAX_VALUE);
                    dayNumber.setAlignment(javafx.geometry.Pos.CENTER);

                    if (currentYearMonth.atDay(day).equals(LocalDate.now())) {
                        dayNumber.setStyle("-fx-font-weight: bold; -fx-font-size: 12px; -fx-padding: 2px; " +
                                         "-fx-background-color: #2196F3; -fx-text-fill: white; -fx-background-radius: 3px;");
                    }

                    LocalDate currentDate = currentYearMonth.atDay(day);
                    List<Appointment> dayAppointments = getAppointmentsForDate(currentDate);
                    for (Appointment appointment : dayAppointments) {
                        HBox appointmentBox = new HBox(2);
                        appointmentBox.setAlignment(javafx.geometry.Pos.CENTER_LEFT);
                        
                        Label appointmentLabel = new Label(appointment.getTitle());
                        appointmentLabel.setStyle("-fx-background-color: " + getColorForGroup(appointment.getGroup()) + 
                                               "; -fx-text-fill: white; -fx-padding: 2px; -fx-background-radius: 2px; " +
                                               "-fx-font-size: 10px;");
                        
                        Button editButton = new Button("✎");
                        editButton.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white; -fx-font-size: 10px; " +
                                          "-fx-min-width: 15px; -fx-min-height: 15px; -fx-padding: 2px; " +
                                          "-fx-background-radius: 2px; -fx-cursor: hand;");
                        editButton.setOnAction(e -> showEditAppointmentDialog(appointment));
                        
                        Button deleteButton = new Button("×");
                        deleteButton.setStyle("-fx-background-color: #F44336; -fx-text-fill: white; -fx-font-size: 10px; " +
                                            "-fx-min-width: 15px; -fx-min-height: 15px; -fx-padding: 2px; " +
                                            "-fx-background-radius: 2px; -fx-cursor: hand;");
                        deleteButton.setOnAction(e -> deleteAppointment(appointment));
                        
                        appointmentBox.getChildren().addAll(appointmentLabel, editButton, deleteButton);
                        dayCell.getChildren().add(appointmentBox);
                    }

                    dayCell.getChildren().add(0, dayNumber);
                    calendarGrid.add(dayCell, dayOfWeekIndex - 1, week);
                    day++;
                }
            }
        }
    }

    private List<Appointment> getAppointmentsForDate(LocalDate date) {
        List<Appointment> dayAppointments = new ArrayList<>();
        for (Appointment appointment : appointments) {
            LocalDate appointmentDate = appointment.getStart().toLocalDate();
            if (appointmentDate.equals(date)) {
                dayAppointments.add(appointment);
            }
        }
        return dayAppointments;
    }

    private String getColorForGroup(String group) {
        return switch (group) {
            case "Hospitalisation" -> "#9C27B0"; // Violet
            case "Consultation" -> "#4CAF50";    // Vert
            case "Urgence" -> "#F44336";         // Rouge
            case "Chirurgie" -> "#2196F3";       // Bleu
            case "Observation" -> "#FF9800";     // Orange
            default -> "#666666";                // Gris
        };
    }

    private void loadSavedAppointments() {
        List<Appointment> savedAppointments = AppointmentPersistence.loadAppointments();
        appointments.addAll(savedAppointments);
    }

    private void saveAppointments() {
        AppointmentPersistence.saveAppointments(appointments);
    }

    public void addAppointment(String title, String description, LocalDateTime start, LocalDateTime end, String group) {
        Appointment appointment = new Appointment(title, description, start, end, group);
        appointments.add(appointment);
        saveAppointments();
        updateCalendar();
    }

    @FXML
    private void showAddAppointmentDialog() {
        Dialog<ButtonType> dialog = new Dialog<>();
        dialog.setTitle("Ajouter un rendez-vous");
        dialog.setHeaderText("Veuillez remplir les détails du rendez-vous");

        TextField titleField = new TextField();
        TextArea descriptionField = new TextArea();
        descriptionField.setPrefRowCount(4);
        DatePicker datePicker = new DatePicker();
        ComboBox<String> hourComboBox = new ComboBox<>();
        ComboBox<String> minuteComboBox = new ComboBox<>();
        ComboBox<String> durationComboBox = new ComboBox<>();
        ComboBox<String> typeComboBox = new ComboBox<>();

        for (int i = 0; i < 24; i++) {
            hourComboBox.getItems().add(String.format("%02d", i));
        }
        for (int i = 0; i < 60; i += 15) {
            minuteComboBox.getItems().add(String.format("%02d", i));
        }
        durationComboBox.getItems().addAll("30 minutes", "1 heure", "1h30", "2 heures", "2h30", "3 heures");
        typeComboBox.getItems().addAll(appointmentGroups);

        hourComboBox.setValue("09");
        minuteComboBox.setValue("00");
        durationComboBox.setValue("1 heure");
        typeComboBox.setValue("Consultation");

        GridPane grid = new GridPane();
        grid.setHgap(10);
        grid.setVgap(10);
        grid.setPadding(new Insets(20, 20, 20, 20));
        
        grid.addRow(0, new Label("Titre:"), titleField);
        grid.addRow(1, new Label("Description:"), descriptionField);
        grid.addRow(2, new Label("Date:"), datePicker);
        grid.addRow(3, new Label("Heure:"), new HBox(5, hourComboBox, new Label(":"), minuteComboBox));
        grid.addRow(4, new Label("Durée:"), durationComboBox);
        grid.addRow(5, new Label("Type:"), typeComboBox);

        dialog.getDialogPane().setContent(grid);
        dialog.getDialogPane().getButtonTypes().addAll(ButtonType.OK, ButtonType.CANCEL);

        Optional<ButtonType> result = dialog.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            int durationMinutes = switch (durationComboBox.getValue()) {
                case "30 minutes" -> 30;
                case "1 heure" -> 60;
                case "1h30" -> 90;
                case "2 heures" -> 120;
                case "2h30" -> 150;
                case "3 heures" -> 180;
                default -> 60;
            };

            LocalDateTime start = datePicker.getValue().atTime(
                    Integer.parseInt(hourComboBox.getValue()),
                    Integer.parseInt(minuteComboBox.getValue())
            );
            LocalDateTime end = start.plusMinutes(durationMinutes);

            addAppointment(titleField.getText(), descriptionField.getText(), start, end, typeComboBox.getValue());
        }
    }

    private void showAppointmentList() {
        Stage listStage = new Stage();
        listStage.initModality(Modality.APPLICATION_MODAL);
        listStage.setTitle("Liste des rendez-vous");

        TableView<Appointment> table = new TableView<>();
        
        TableColumn<Appointment, String> titleCol = new TableColumn<>("Titre");
        titleCol.setCellValueFactory(data -> new SimpleStringProperty(data.getValue().getTitle()));
        
        TableColumn<Appointment, String> dateCol = new TableColumn<>("Date et heure");
        dateCol.setCellValueFactory(data -> new SimpleStringProperty(
            data.getValue().getStart().format(DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm"))
        ));
        
        TableColumn<Appointment, String> typeCol = new TableColumn<>("Type");
        typeCol.setCellValueFactory(data -> new SimpleStringProperty(data.getValue().getGroup()));

        TableColumn<Appointment, Void> actionsCol = new TableColumn<>("Actions");
        actionsCol.setCellFactory(param -> new TableCell<>() {
            private final Button editButton = new Button("✎");
            private final Button deleteButton = new Button("×");
            private final HBox buttons = new HBox(5, editButton, deleteButton);

            {
                editButton.setStyle("-fx-background-color: #4CAF50; -fx-text-fill: white; -fx-font-size: 14px; " +
                                  "-fx-min-width: 30px; -fx-min-height: 30px; -fx-padding: 5px; " +
                                  "-fx-background-radius: 3px; -fx-cursor: hand;");
                deleteButton.setStyle("-fx-background-color: #F44336; -fx-text-fill: white; -fx-font-size: 14px; " +
                                    "-fx-min-width: 30px; -fx-min-height: 30px; -fx-padding: 5px; " +
                                    "-fx-background-radius: 3px; -fx-cursor: hand;");

                editButton.setOnAction(event -> {
                    Appointment appointment = getTableView().getItems().get(getIndex());
                    showEditAppointmentDialog(appointment);
                });

                deleteButton.setOnAction(event -> {
                    Appointment appointment = getTableView().getItems().get(getIndex());
                    deleteAppointment(appointment);
                });
            }

            @Override
            protected void updateItem(Void item, boolean empty) {
                super.updateItem(item, empty);
                if (empty) {
                    setGraphic(null);
                } else {
                    setGraphic(buttons);
                }
            }
        });

        table.getColumns().addAll(titleCol, dateCol, typeCol, actionsCol);
        table.setItems(appointments);

        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().add(table);

        Scene scene = new Scene(layout, 800, 400);
        listStage.setScene(scene);
        listStage.show();
    }

    private void showEditAppointmentDialog(Appointment appointment) {
        Dialog<ButtonType> dialog = new Dialog<>();
        dialog.setTitle("Modifier le rendez-vous");
        dialog.setHeaderText("Modifiez les détails du rendez-vous");

        TextField titleField = new TextField(appointment.getTitle());
        TextArea descriptionField = new TextArea(appointment.getDescription());
        descriptionField.setPrefRowCount(4);
        DatePicker datePicker = new DatePicker(appointment.getStart().toLocalDate());
        ComboBox<String> hourComboBox = new ComboBox<>();
        ComboBox<String> minuteComboBox = new ComboBox<>();
        ComboBox<String> durationComboBox = new ComboBox<>();
        ComboBox<String> typeComboBox = new ComboBox<>();

        for (int i = 0; i < 24; i++) {
            hourComboBox.getItems().add(String.format("%02d", i));
        }
        for (int i = 0; i < 60; i += 15) {
            minuteComboBox.getItems().add(String.format("%02d", i));
        }
        durationComboBox.getItems().addAll("30 minutes", "1 heure", "1h30", "2 heures", "2h30", "3 heures");
        typeComboBox.getItems().addAll(appointmentGroups);

        hourComboBox.setValue(String.format("%02d", appointment.getStart().getHour()));
        minuteComboBox.setValue(String.format("%02d", appointment.getStart().getMinute()));
        long currentDurationMinutes = java.time.Duration.between(appointment.getStart(), appointment.getEnd()).toMinutes();
        durationComboBox.setValue(getDurationString(currentDurationMinutes));
        typeComboBox.setValue(appointment.getGroup());

        GridPane grid = new GridPane();
        grid.setHgap(10);
        grid.setVgap(10);
        grid.setPadding(new Insets(20, 20, 20, 20));
        
        grid.addRow(0, new Label("Titre:"), titleField);
        grid.addRow(1, new Label("Description:"), descriptionField);
        grid.addRow(2, new Label("Date:"), datePicker);
        grid.addRow(3, new Label("Heure:"), new HBox(5, hourComboBox, new Label(":"), minuteComboBox));
        grid.addRow(4, new Label("Durée:"), durationComboBox);
        grid.addRow(5, new Label("Type:"), typeComboBox);

        dialog.getDialogPane().setContent(grid);
        dialog.getDialogPane().getButtonTypes().addAll(ButtonType.OK, ButtonType.CANCEL);

        Optional<ButtonType> result = dialog.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            int newDurationMinutes = switch (durationComboBox.getValue()) {
                case "30 minutes" -> 30;
                case "1 heure" -> 60;
                case "1h30" -> 90;
                case "2 heures" -> 120;
                case "2h30" -> 150;
                case "3 heures" -> 180;
                default -> 60;
            };

            LocalDateTime start = datePicker.getValue().atTime(
                    Integer.parseInt(hourComboBox.getValue()),
                    Integer.parseInt(minuteComboBox.getValue())
            );
            LocalDateTime end = start.plusMinutes(newDurationMinutes);

            appointment.setTitle(titleField.getText());
            appointment.setDescription(descriptionField.getText());
            appointment.setStart(start);
            appointment.setEnd(end);
            appointment.setGroup(typeComboBox.getValue());

            saveAppointments();
            updateCalendar();
        }
    }

    private String getDurationString(long minutes) {
        return switch ((int) minutes) {
            case 30 -> "30 minutes";
            case 60 -> "1 heure";
            case 90 -> "1h30";
            case 120 -> "2 heures";
            case 150 -> "2h30";
            case 180 -> "3 heures";
            default -> "1 heure";
        };
    }

    private void deleteAppointment(Appointment appointment) {
        Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
        alert.setTitle("Confirmation de suppression");
        alert.setHeaderText("Supprimer le rendez-vous");
        alert.setContentText("Êtes-vous sûr de vouloir supprimer ce rendez-vous ?");

        Optional<ButtonType> result = alert.showAndWait();
        if (result.isPresent() && result.get() == ButtonType.OK) {
            appointments.remove(appointment);
            saveAppointments();
            updateCalendar();
        }
    }
} 