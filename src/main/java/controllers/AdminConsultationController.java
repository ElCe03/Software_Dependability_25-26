package controllers;

import entite.Consultation;
import javafx.animation.PauseTransition;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.collections.FXCollections;
import javafx.fxml.FXML;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.print.PrinterJob;
import javafx.scene.Scene;
import javafx.scene.chart.BarChart;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.PieChart;
import javafx.scene.chart.XYChart;
import javafx.scene.control.*;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.image.Image;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.shape.SVGPath;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.Stage;
import javafx.stage.StageStyle;
import javafx.util.Callback;
import javafx.util.Duration;
import service.ConsultationService;
import service.TwilioSMSService;

import java.text.SimpleDateFormat;
import java.time.LocalDate;
import java.util.*;
import java.util.prefs.Preferences;
import java.util.stream.Collectors;

public class AdminConsultationController {
    @FXML private TableView<Consultation> consultationTable;
    @FXML private TextField searchField;
    @FXML private ComboBox<String> statusFilterCombo;
    @FXML private Button statsButton;
    @FXML private Button pieChartButton;
    @FXML private Button exportPdfButton;
    @FXML private Button mostLikedButton;

    private final ConsultationService consultationService = new ConsultationService();
    private final TwilioSMSService twilioService = new TwilioSMSService();
    private final Preferences prefs = Preferences.userNodeForPackage(AdminConsultationController.class);

    @FXML
    public void initialize() {
        verifyTwilioSetup();
        setupTableColumns();
        setupStatusFilter();
        refreshTable();

        statsButton.setOnAction(event -> showHorizontalBarChartStatistics());
        pieChartButton.setOnAction(event -> showPieChartStatistics());
        exportPdfButton.setOnAction(event -> exportToPdf());
        mostLikedButton.setOnAction(event -> showMostLikedServices());
    }

    private void verifyTwilioSetup() {
        if (!twilioService.isConfigured()) {
            System.err.println("Twilio not properly configured in config.properties!");
            showAlert("Configuration Error",
                    "Twilio SMS is not configured properly. Check config.properties file.");
        }
    }

    private void setupTableColumns() {
        consultationTable.getColumns().clear();

        TableColumn<Consultation, Integer> idCol = new TableColumn<>("ID");
        idCol.setCellValueFactory(new PropertyValueFactory<>("id"));
        idCol.setPrefWidth(50);

        TableColumn<Consultation, String> serviceCol = new TableColumn<>("Service");
        serviceCol.setCellValueFactory(new PropertyValueFactory<>("serviceName"));
        serviceCol.setPrefWidth(150);

        TableColumn<Consultation, Date> dateCol = new TableColumn<>("Date");
        dateCol.setCellValueFactory(new PropertyValueFactory<>("date"));
        dateCol.setPrefWidth(120);
        dateCol.setCellFactory(column -> new TableCell<Consultation, Date>() {
            private final SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd HH:mm");

            @Override
            protected void updateItem(Date date, boolean empty) {
                super.updateItem(date, empty);
                if (empty || date == null) {
                    setText(null);
                } else {
                    setText(format.format(date));
                }
            }
        });

        TableColumn<Consultation, String> patientCol = new TableColumn<>("Patient ID");
        patientCol.setCellValueFactory(new PropertyValueFactory<>("patientIdentifier"));
        patientCol.setPrefWidth(100);

        TableColumn<Consultation, String> phoneCol = new TableColumn<>("Phone");
        phoneCol.setCellValueFactory(new PropertyValueFactory<>("phoneNumber"));
        phoneCol.setPrefWidth(100);

        TableColumn<Consultation, String> statusCol = new TableColumn<>("Status");
        statusCol.setCellValueFactory(new PropertyValueFactory<>("status"));
        statusCol.setCellFactory(new StatusCellFactory());
        statusCol.setPrefWidth(100);
        statusCol.setEditable(true);

        TableColumn<Consultation, Integer> ratingCol = new TableColumn<>("Rating");
        ratingCol.setPrefWidth(80);
        ratingCol.setCellValueFactory(cellData -> {
            Consultation c = cellData.getValue();
            return new SimpleIntegerProperty(getRatingForConsultation(c.getId())).asObject();
        });
        ratingCol.setCellFactory(column -> new TableCell<Consultation, Integer>() {
            private final HBox starsContainer = new HBox(2);

            @Override
            protected void updateItem(Integer rating, boolean empty) {
                super.updateItem(rating, empty);
                if (empty || rating == null) {
                    setGraphic(null);
                } else {
                    starsContainer.getChildren().clear();
                    for (int i = 1; i <= 5; i++) {
                        SVGPath star = new SVGPath();
                        star.setContent("M12 .587l3.668 7.568 8.332 1.151-6.064 5.828 1.48 8.279-7.416-3.967-7.417 3.967 1.481-8.279-6.064-5.828 8.332-1.151z");
                        star.setFill(i <= rating ? Color.GOLD : Color.LIGHTGRAY);
                        starsContainer.getChildren().add(star);
                    }
                    setGraphic(starsContainer);
                }
            }
        });

        consultationTable.getColumns().addAll(idCol, serviceCol, dateCol, patientCol, phoneCol, statusCol, ratingCol);
        consultationTable.setEditable(true);
    }

    private void showMostLikedServices() {
        List<Consultation> consultations = consultationService.getAllConsultations();

        // Group consultations by service and calculate average rating
        Map<String, Double> serviceRatings = consultations.stream()
                .filter(c -> getRatingForConsultation(c.getId()) > 0) // Only include rated consultations
                .collect(Collectors.groupingBy(
                        Consultation::getServiceName,
                        Collectors.averagingDouble(c -> getRatingForConsultation(c.getId()))
                ));

        // Sort by average rating (descending) and get top 5
        List<Map.Entry<String, Double>> topServices = serviceRatings.entrySet().stream()
                .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                .limit(5)
                .collect(Collectors.toList());

        if (topServices.isEmpty()) {
            showAlert("No Ratings", "No services have been rated yet.");
            return;
        }

        showMostLikedServicesDialog(topServices);
    }

    private void showMostLikedServicesDialog(List<Map.Entry<String, Double>> topServices) {
        Stage dialog = new Stage();
        dialog.setTitle("Most Liked Services");

        VBox vbox = new VBox(10);
        vbox.setPadding(new Insets(15));
        vbox.setAlignment(Pos.CENTER);

        Label title = new Label("⭐ Most Liked Services ⭐");
        title.setStyle("-fx-font-size: 18px; -fx-font-weight: bold;");

        ListView<HBox> listView = new ListView<>();
        listView.setPrefSize(400, 300);

        for (Map.Entry<String, Double> entry : topServices) {
            HBox item = createServiceRatingItem(entry.getKey(), entry.getValue());
            listView.getItems().add(item);
        }

        vbox.getChildren().addAll(title, listView);

        Scene scene = new Scene(vbox);
        dialog.setScene(scene);
        dialog.show();
    }

    private HBox createServiceRatingItem(String serviceName, double averageRating) {
        HBox hbox = new HBox(10);
        hbox.setAlignment(Pos.CENTER_LEFT);
        hbox.setPadding(new Insets(5));

        // Service name
        Label serviceLabel = new Label(serviceName);
        serviceLabel.setStyle("-fx-font-weight: bold; -fx-font-size: 14px;");
        serviceLabel.setPrefWidth(150);

        // Star rating visualization
        HBox stars = new HBox(2);
        int roundedRating = (int) Math.round(averageRating);
        for (int i = 1; i <= 5; i++) {
            SVGPath star = new SVGPath();
            star.setContent("M12 .587l3.668 7.568 8.332 1.151-6.064 5.828 1.48 8.279-7.416-3.967-7.417 3.967 1.481-8.279-6.064-5.828 8.332-1.151z");
            star.setFill(i <= roundedRating ? Color.GOLD : Color.LIGHTGRAY);
            stars.getChildren().add(star);
        }

        // Average rating text
        Label ratingLabel = new Label(String.format("(Avg: %.1f)", averageRating));
        ratingLabel.setStyle("-fx-font-size: 12px; -fx-text-fill: #555;");

        hbox.getChildren().addAll(serviceLabel, stars, ratingLabel);
        return hbox;
    }

    @FXML
    private void exportToPdf() {
        try {
            // Create HTML content with logo and table data
            StringBuilder html = new StringBuilder();
            html.append("<html><head><style>")
                    .append("body { font-family: Arial, sans-serif; margin: 20px; }")
                    .append(".header { display: flex; align-items: center; margin-bottom: 20px; }")
                    .append(".logo { height: 80px; margin-right: 20px; }")
                    .append(".title { flex-grow: 1; }")
                    .append("h1 { margin: 0; color: #2c3e50; }")
                    .append(".date { color: #7f8c8d; font-size: 14px; }")
                    .append("table { width: 100%; border-collapse: collapse; margin-top: 20px; }")
                    .append("th { background-color: #3498db; color: white; text-align: left; padding: 10px; }")
                    .append("td { padding: 8px; border-bottom: 1px solid #ddd; }")
                    .append("tr:nth-child(even) { background-color: #f2f2f2; }")
                    .append(".footer { margin-top: 20px; text-align: right; font-size: 12px; color: #7f8c8d; }")
                    .append("</style></head><body>")
                    .append("<div class='header'>")
                    .append("<img class='logo' src='").append(getClass().getResource("/img/logo.png")).append("'/>")
                    .append("<div class='title'>")
                    .append("<h1>Consultation Report</h1>")
                    .append("<div class='date'>Generated on: ").append(LocalDate.now()).append("</div>")
                    .append("</div></div>")
                    .append("<table><thead><tr>");

            // Add table headers
            for (TableColumn<Consultation, ?> column : consultationTable.getColumns()) {
                html.append("<th>").append(column.getText()).append("</th>");
            }
            html.append("</tr></thead><tbody>");

            // Add table data
            for (Consultation item : consultationTable.getItems()) {
                html.append("<tr>")
                        .append("<td>").append(item.getId()).append("</td>")
                        .append("<td>").append(item.getServiceName()).append("</td>")
                        .append("<td>").append(new SimpleDateFormat("yyyy-MM-dd HH:mm").format(item.getDate())).append("</td>")
                        .append("<td>").append(item.getPatientIdentifier()).append("</td>")
                        .append("<td>").append(item.getPhoneNumber()).append("</td>")
                        .append("<td>").append(item.getStatus()).append("</td>")
                        .append("<td>").append(getRatingStars(getRatingForConsultation(item.getId()))).append("</td>")
                        .append("</tr>");
            }

            html.append("</tbody></table>")
                    .append("<div class='footer'>")
                    .append("Total consultations: ").append(consultationTable.getItems().size())
                    .append("</div></body></html>");

            // Create WebView to render HTML
            WebView webView = new WebView();
            WebEngine webEngine = webView.getEngine();
            webEngine.loadContent(html.toString());

            // Create printer job
            PrinterJob job = PrinterJob.createPrinterJob();
            if (job != null && job.showPrintDialog(consultationTable.getScene().getWindow())) {
                webEngine.print(job);
                job.endJob();
                showNotification("PDF exported successfully with logo");
            }
        } catch (Exception e) {
            showAlert("PDF Export Error", "Error during PDF export: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private String getRatingStars(int rating) {
        StringBuilder stars = new StringBuilder();
        for (int i = 0; i < 5; i++) {
            stars.append(i < rating ? "★" : "☆");
        }
        return stars.toString();
    }

    private int getRatingForConsultation(int consultationId) {
        String savedRatings = prefs.get("consultation_ratings", "");
        if (!savedRatings.isEmpty()) {
            String[] pairs = savedRatings.split(";");
            for (String pair : pairs) {
                String[] keyValue = pair.split(":");
                if (keyValue.length == 2 && Integer.parseInt(keyValue[0]) == consultationId) {
                    return Integer.parseInt(keyValue[1]);
                }
            }
        }
        return 0;
    }

    private void saveRatingForConsultation(int consultationId, int rating) {
        String savedRatings = prefs.get("consultation_ratings", "");
        Map<String, String> ratingsMap = new HashMap<>();

        if (!savedRatings.isEmpty()) {
            String[] pairs = savedRatings.split(";");
            for (String pair : pairs) {
                String[] keyValue = pair.split(":");
                if (keyValue.length == 2) {
                    ratingsMap.put(keyValue[0], keyValue[1]);
                }
            }
        }

        ratingsMap.put(String.valueOf(consultationId), String.valueOf(rating));

        String newRatings = ratingsMap.entrySet().stream()
                .map(entry -> entry.getKey() + ":" + entry.getValue())
                .collect(Collectors.joining(";"));

        prefs.put("consultation_ratings", newRatings);
    }

    private void setupStatusFilter() {
        statusFilterCombo.getItems().addAll("All", "En cours de traitement", "Confirmed", "Done");
        statusFilterCombo.getSelectionModel().selectFirst();
        statusFilterCombo.setOnAction(event -> refreshTable());
    }

    @FXML
    private void handleSearch() {
        refreshTable();
    }

    @FXML
    private void handleRefresh() {
        searchField.clear();
        statusFilterCombo.getSelectionModel().selectFirst();
        refreshTable();
    }

    private void refreshTable() {
        String searchTerm = searchField.getText().trim();
        String statusFilter = statusFilterCombo.getValue();

        List<Consultation> consultations;
        if (searchTerm.isEmpty()) {
            consultations = consultationService.getAllConsultations();
        } else {
            consultations = consultationService.searchConsultations(searchTerm);
        }

        if (!"All".equals(statusFilter)) {
            consultations = consultations.stream()
                    .filter(c -> c.getStatus().equals(statusFilter))
                    .collect(Collectors.toList());
        }

        consultationTable.setItems(FXCollections.observableArrayList(consultations));
    }

    private void showHorizontalBarChartStatistics() {
        List<Consultation> consultations = consultationService.getAllConsultations();

        Map<String, Long> serviceCounts = consultations.stream()
                .collect(Collectors.groupingBy(
                        Consultation::getServiceName,
                        Collectors.counting()
                ));

        NumberAxis xAxis = new NumberAxis();
        xAxis.setLabel("Number of Consultations");
        xAxis.setTickUnit(1);
        xAxis.setMinorTickVisible(false);

        CategoryAxis yAxis = new CategoryAxis();
        yAxis.setLabel("Service");
        yAxis.setTickLabelRotation(0);

        BarChart<Number, String> barChart = new BarChart<>(xAxis, yAxis);
        barChart.setTitle("Consultations by Service (Horizontal)");
        barChart.setCategoryGap(20);
        barChart.setLegendVisible(false);

        XYChart.Series<Number, String> series = new XYChart.Series<>();
        series.setName("Services");

        serviceCounts.entrySet().stream()
                .sorted(Map.Entry.<String, Long>comparingByValue().reversed())
                .forEach(entry ->
                        series.getData().add(new XYChart.Data<>(entry.getValue(), entry.getKey()))
                );

        barChart.getData().add(series);

        for (XYChart.Data<Number, String> data : series.getData()) {
            data.getNode().setStyle("-fx-bar-fill: #3498db;");
        }

        Stage chartStage = new Stage();
        chartStage.setTitle("Consultation Statistics - Horizontal Bar Chart");
        VBox vbox = new VBox(barChart);
        Scene scene = new Scene(vbox, 800, 600);
        chartStage.setScene(scene);
        chartStage.show();
    }

    private void showPieChartStatistics() {
        List<Consultation> consultations = consultationService.getAllConsultations();

        Map<String, Long> serviceCounts = consultations.stream()
                .collect(Collectors.groupingBy(
                        Consultation::getServiceName,
                        Collectors.counting()
                ));

        PieChart pieChart = new PieChart();
        pieChart.setTitle("Consultations by Service");
        pieChart.setLabelLineLength(10);
        pieChart.setLegendVisible(true);

        serviceCounts.forEach((service, count) ->
                pieChart.getData().add(new PieChart.Data(service + " (" + count + ")", count))
        );

        Stage chartStage = new Stage();
        chartStage.setTitle("Consultation Statistics - Pie Chart");
        VBox vbox = new VBox(pieChart);
        Scene scene = new Scene(vbox, 600, 500);
        chartStage.setScene(scene);
        chartStage.show();
    }

    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }

    private void showNotification(String message) {
        Stage notificationStage = new Stage();
        notificationStage.initStyle(StageStyle.TRANSPARENT);

        Label label = new Label(message);
        label.setStyle("-fx-text-fill: white; -fx-font-size: 14px; -fx-padding: 10px;");

        StackPane root = new StackPane(label);
        root.setStyle("-fx-background-color: rgba(0, 100, 200, 0.8); -fx-background-radius: 10;");

        Scene scene = new Scene(root);
        scene.setFill(Color.TRANSPARENT);
        notificationStage.setScene(scene);

        notificationStage.setX(javafx.stage.Screen.getPrimary().getVisualBounds().getWidth() - 350);
        notificationStage.setY(20);

        notificationStage.show();

        PauseTransition delay = new PauseTransition(Duration.seconds(3));
        delay.setOnFinished(event -> notificationStage.close());
        delay.play();
    }

    private class StatusCellFactory implements Callback<TableColumn<Consultation, String>,
            TableCell<Consultation, String>> {

        @Override
        public TableCell<Consultation, String> call(TableColumn<Consultation, String> param) {
            return new TableCell<>() {
                private final ComboBox<String> comboBox = new ComboBox<>();

                {
                    comboBox.getItems().addAll("En cours de traitement", "Confirmed", "Done");
                    comboBox.setOnAction(event -> {
                        if (getTableRow() != null && getTableRow().getItem() != null) {
                            Consultation consultation = getTableRow().getItem();
                            String oldStatus = consultation.getStatus();
                            String newStatus = comboBox.getValue();

                            if (!newStatus.equals(oldStatus)) {
                                if (consultationService.updateConsultationStatus(
                                        consultation.getId(), newStatus)) {
                                    consultation.setStatus(newStatus);

                                    handleSmsNotification(consultation, newStatus);
                                    refreshTable();
                                } else {
                                    showAlert("Error", "Failed to update status");
                                }
                            }
                        }
                    });
                }

                @Override
                protected void updateItem(String status, boolean empty) {
                    super.updateItem(status, empty);
                    if (empty || status == null) {
                        setText(null);
                        setGraphic(null);
                        setStyle("");
                    } else {
                        comboBox.setValue(status);
                        setGraphic(comboBox);

                        switch (status) {
                            case "En cours de traitement":
                                setStyle("-fx-background-color: #fff3cd;");
                                break;
                            case "Confirmed":
                                setStyle("-fx-background-color: #d4edda;");
                                break;
                            case "Done":
                                setStyle("-fx-background-color: #f8d7da;");
                                break;
                            default:
                                setStyle("");
                        }
                    }
                }
            };
        }
    }

    private void handleSmsNotification(Consultation consultation, String newStatus) {
        if (!twilioService.isConfigured()) {
            showNotification("Status updated (SMS not configured)");
            return;
        }

        try {
            String phoneNumber = consultation.getPhoneNumber();
            String message = buildSmsMessage(consultation, newStatus);

            String smsResult = twilioService.sendSMS(phoneNumber, message);

            if (smsResult.contains("successfully")) {
                showNotification("Status updated & SMS sent to " +
                        consultation.getPatientIdentifier());
            } else {
                showAlert("SMS Failed", "Status updated but SMS failed: " + smsResult);
            }
        } catch (Exception e) {
            showAlert("SMS Error", "Error sending SMS: " + e.getMessage());
        }
    }

    private String buildSmsMessage(Consultation consultation, String newStatus) {
        return String.format(
                "Dear %s,%n" +
                        "Your consultation status is now: %s%n" +
                        "%s%n" +
                        "Thank you!",
                consultation.getPatientIdentifier(),
                newStatus,
                getStatusSpecificMessage(newStatus)
        );
    }

    private String getStatusSpecificMessage(String status) {
        switch (status) {
            case "En cours de traitement":
                return "We are currently processing your request. Thank you for your patience.";
            case "Confirmed":
                return "Your appointment has been confirmed. We look forward to seeing you.";
            case "Done":
                return "We hope you had a great experience with us!";
            default:
                return "";
        }
    }
}