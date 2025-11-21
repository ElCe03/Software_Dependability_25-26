package controllers;

import entite.departement;
import entite.etage;
import entite.salle;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.*;
import javafx.scene.shape.SVGPath;
import javafx.scene.web.WebView;
import javafx.stage.Modality;
import javafx.stage.Stage;
import org.json.JSONObject;
import service.DepartemntService;
import service.EtageService;
import service.SalleService;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.List;

public class Listdepartement {

    private final DepartemntService departementService = new DepartemntService();
    private final EtageService etageService = new EtageService();
    private final SalleService salleService = new SalleService();
    private static final String OPENCAGE_API_KEY = "47d253d97db14316aa01c6ff2d659492";

    @FXML private FlowPane departementContainer;
    @FXML private TextField searchBar;
    @FXML private Button moreInfoButton;
    @FXML private Button backButton;

    @FXML
    public void initialize() {
        loadAllDepartments();
        searchBar.textProperty().addListener((obs, oldVal, newVal) -> searchDepartments(newVal));

        departementContainer.setHgap(20);
        departementContainer.setVgap(20);
        departementContainer.setPadding(new Insets(15));

        // Handle More Info Button (Chatbot)
        moreInfoButton.setOnAction(e -> showChatbotDialog());
    }

    private void loadAllDepartments() {
        departementContainer.getChildren().clear();
        List<departement> allDepartments = departementService.getAllDepartements();
        for (departement dept : allDepartments) {
            departementContainer.getChildren().add(createDepartmentCard(dept));
        }
    }

    private Node createDepartmentCard(departement department) {
        VBox container = new VBox(10);
        container.setAlignment(Pos.CENTER_LEFT);

        // Modern Card Design
        VBox card = new VBox(10);
        card.getStyleClass().add("department-card");
        card.setAlignment(Pos.CENTER);
        card.setPrefWidth(300);
        card.setPadding(new Insets(15));
        card.setEffect(new javafx.scene.effect.DropShadow(10, 0, 5, javafx.scene.paint.Color.gray(0.5)));

        // Image
        ImageView imageView = new ImageView();
        loadDepartmentImage(imageView, department.getImage());
        imageView.setFitWidth(270);
        imageView.setFitHeight(150);
        imageView.setStyle("-fx-background-radius: 10;");

        // Title
        Label title = new Label(department.getNom());
        title.getStyleClass().add("department-card-title");

        // Details
        int floorCount = etageService.getEtagesByDepartement(department.getId()).size();
        Label details = new Label(String.format("%d étages • %s", floorCount, department.getAdresse()));
        details.getStyleClass().add("department-card-details");

        // Voir détails Button
        Button detailsButton = new Button("Voir détails");
        detailsButton.getStyleClass().add("details-button");
        detailsButton.setOnAction(e -> showDetailsDialog(department));

        // Floors Container
        VBox floorsContainerForThisDepartment = new VBox(10);
        floorsContainerForThisDepartment.setPadding(new Insets(10, 20, 10, 50));
        floorsContainerForThisDepartment.setVisible(false);

        // Card Click for Floors
        card.setOnMouseClicked(e -> {
            if (floorsContainerForThisDepartment.isVisible()) {
                floorsContainerForThisDepartment.setVisible(false);
                floorsContainerForThisDepartment.getChildren().clear();
            } else {
                floorsContainerForThisDepartment.setVisible(true);
                showFloorsUnderDepartment(department, floorsContainerForThisDepartment);
            }
        });

        card.getChildren().addAll(imageView, title, details, detailsButton);
        container.getChildren().addAll(card, floorsContainerForThisDepartment);
        return container;
    }
    private double[] geocodeAddress(String address) {
        try {
            String encodedAddress = URLEncoder.encode(address, StandardCharsets.UTF_8);
            String urlString = "https://maps.googleapis.com/maps/api/geocode/json?address="
                    + encodedAddress + "&key=AIzaSyAJEuwo_pOrUzusQG6CS04gUCzu2_a-OQg";

            URL url = new URL(urlString);
            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
            conn.setRequestMethod("GET");

            if (conn.getResponseCode() == 200) {
                BufferedReader in = new BufferedReader(new InputStreamReader(conn.getInputStream()));
                StringBuilder response = new StringBuilder();
                String inputLine;

                while ((inputLine = in.readLine()) != null) {
                    response.append(inputLine);
                }
                in.close();

                // Parse JSON response
                JSONObject jsonResponse = new JSONObject(response.toString());
                if (jsonResponse.has("results") && jsonResponse.getJSONArray("results").length() > 0) {
                    JSONObject location = jsonResponse.getJSONArray("results")
                            .getJSONObject(0)
                            .getJSONObject("geometry")
                            .getJSONObject("location");

                    return new double[]{
                            location.getDouble("lat"),
                            location.getDouble("lng")
                    };
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null; // Retourne null si le géocodage échoue
    }

    private void showDetailsDialog(departement department) {
        Stage dialog = new Stage();
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Détails de " + department.getNom());
        dialog.setWidth(800);
        dialog.setHeight(600);

        BorderPane layout = new BorderPane();
        layout.setPadding(new Insets(10));

        // Details Section (inchangé)
        VBox detailsBox = new VBox(10);
        detailsBox.setPadding(new Insets(10));
        detailsBox.setStyle("-fx-background-color: #ffffff; -fx-background-radius: 10; -fx-border-radius: 10; -fx-border-color: #e0e0e0; -fx-border-width: 1;");

        Label nameLabel = new Label("Nom: " + department.getNom());
        nameLabel.setStyle("-fx-font-size: 16px; -fx-font-weight: bold;");

        int floorCount = etageService.getEtagesByDepartement(department.getId()).size();
        Label floorsLabel = new Label("Nombre d'étages: " + floorCount);
        floorsLabel.setStyle("-fx-font-size: 14px;");

        Label addressLabel = new Label("Adresse: " + department.getAdresse());
        addressLabel.setStyle("-fx-font-size: 14px;");

        detailsBox.getChildren().addAll(nameLabel, floorsLabel, addressLabel);
        layout.setLeft(detailsBox);

        // Google Maps Section
        WebView mapView = new WebView();
        mapView.setPrefSize(500, 500);

        double[] coordinates = geocodeAddress(department.getAdresse());
        String htmlContent;
        if (coordinates != null) {
            double lat = coordinates[0];
            double lng = coordinates[1];
            String sanitizedDeptName = department.getNom()
                    .replace("'", "\\'")
                    .replace("\"", "\\\"");

            htmlContent = """
            <!DOCTYPE html>
            <html>
            <head>
                <title>Google Maps</title>
                <style>
                    #map { height: 100%; width: 100%; }
                    body { margin: 0; padding: 0; }
                </style>
            </head>
            <body>
                <div id="map"></div>
                <script>
                    function initMap() {
                        var location = { lat: %f, lng: %f };
                        var map = new google.maps.Map(document.getElementById('map'), {
                            zoom: 15,
                            center: location
                        });
                        var marker = new google.maps.Marker({
                            position: location,
                            map: map,
                            title: '%s'
                        });
                    }
                </script>
                <script async defer
                    src="https://maps.googleapis.com/maps/api/js?key=%s&callback=initMap">
                </script>
            </body>
            </html>
            """.formatted(lat, lng, sanitizedDeptName, "AIzaSyAJEuwo_pOrUzusQG6CS04gUCzu2_a-OQg");
        } else {
            htmlContent = """
            <html><body>
                <p style='color:red;padding:20px;'>
                    Impossible de charger la carte pour l'adresse: %s
                </p>
            </body></html>
            """.formatted(department.getAdresse().replace("'", "\\'"));
        }

        mapView.getEngine().loadContent(htmlContent);

        // Error handling
        mapView.getEngine().setOnError(event -> {
            System.err.println("Map loading error: " + event.getMessage());
        });

        layout.setCenter(mapView);

        // Close Button (inchangé)
        Button closeButton = new Button("Fermer");
        closeButton.setStyle("-fx-background-color: #4a90e2; -fx-text-fill: white; -fx-font-weight: bold; -fx-background-radius: 20; -fx-padding: 8 20;");
        closeButton.setOnAction(e -> dialog.close());

        HBox buttonBox = new HBox(closeButton);
        buttonBox.setAlignment(Pos.CENTER_RIGHT);
        buttonBox.setPadding(new Insets(10));
        layout.setBottom(buttonBox);

        javafx.scene.Scene scene = new javafx.scene.Scene(layout);
        dialog.setScene(scene);
        dialog.showAndWait();
    }

    private void showChatbotDialog() {
        // Create a new stage for the chatbo
        Stage dialog = new Stage();
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Informations");
        dialog.setWidth(600);
        dialog.setHeight(700);

        // Create WebView to load the chatbot
        WebView webView = new WebView();
        webView.getEngine().load("https://www.chatbase.co/chatbot-iframe/mqDWyeqN2lfN8X8xHVULD");

        // Layout for the dialog
        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().add(webView);

        // Scene and Stage
        javafx.scene.Scene scene = new javafx.scene.Scene(layout);
        dialog.setScene(scene);
        dialog.showAndWait();
    }

    private void showFloorsUnderDepartment(departement department, VBox floorsContainer) {
        floorsContainer.getChildren().clear();
        List<etage> floors = etageService.getEtagesByDepartement(department.getId());

        if (floors.isEmpty()) {
            Label noFloorsLabel = new Label("Ce département n'a pas encore d'étages");
            noFloorsLabel.setStyle("-fx-text-fill: #666; -fx-font-size: 14px;");
            floorsContainer.getChildren().add(noFloorsLabel);
        } else {
            for (etage floor : floors) {
                VBox floorContainer = new VBox(5);

                Node floorCard = createFloorCard(floor);
                VBox roomsContainer = new VBox(5);
                roomsContainer.setPadding(new Insets(5, 20, 5, 50));
                roomsContainer.setVisible(false);

                floorCard.setOnMouseClicked(event -> {
                    if (roomsContainer.isVisible()) {
                        roomsContainer.setVisible(false);
                        roomsContainer.getChildren().clear();
                    } else {
                        roomsContainer.setVisible(true);
                        loadRoomsUnderFloor(floor, roomsContainer);
                    }
                });

                floorContainer.getChildren().addAll(floorCard, roomsContainer);
                floorsContainer.getChildren().add(floorContainer);
            }
        }
    }

    private void loadRoomsUnderFloor(etage floor, VBox roomsContainer) {
        roomsContainer.getChildren().clear();
        List<salle> rooms = salleService.getAll().stream()
                .filter(r -> r.getEtage() != null && r.getEtage().getId() == floor.getId())
                .toList();

        if (rooms.isEmpty()) {
            Label noRoomsLabel = new Label("Aucune salle sur cet étage");
            noRoomsLabel.setStyle("-fx-text-fill: #999; -fx-font-size: 13px;");
            roomsContainer.getChildren().add(noRoomsLabel);
        } else {
            for (salle room : rooms) {
                roomsContainer.getChildren().add(createRoomCard(room));
            }
        }
    }

    private Node createFloorCard(etage floor) {
        VBox card = new VBox(8);
        card.getStyleClass().add("floor-card");
        card.setAlignment(Pos.CENTER);
        card.setPrefWidth(200);

        SVGPath icon = new SVGPath();
        icon.setContent("M19,3H5C3.9,3,3,3.9,3,5v14c0,1.1,0.9,2,2,2h14c1.1,0,2-0.9,2-2V5C21,3.9,20.1,3,19,3z M19,19H5V5h14V19z");
        icon.setStyle("-fx-fill: #4a90e2;");

        Label title = new Label("Étage " + floor.getNumero());
        title.setStyle("-fx-font-weight: bold; -fx-font-size: 14px;");

        long roomCount = salleService.getAll().stream()
                .filter(r -> r.getEtage() != null && r.getEtage().getId() == floor.getId())
                .count();

        Label details = new Label(roomCount + (roomCount > 1 ? " salles" : " salle"));
        details.setStyle("-fx-text-fill: #6c757d; -fx-font-size: 13px;");

        card.getChildren().addAll(icon, title, details);
        return card;
    }

    private Node createRoomCard(salle room) {
        VBox card = new VBox(5);
        card.getStyleClass().add("room-card");
        card.setAlignment(Pos.CENTER);
        card.setPrefWidth(150);

        ImageView imageView = new ImageView();
        loadRoomImage(imageView, room.getImage());
        imageView.setFitWidth(120);
        imageView.setFitHeight(80);

        Label title = new Label(room.getNom());
        title.setStyle("-fx-font-weight: bold; -fx-text-alignment: center;");

        Label details = new Label(
                String.format("%s\n%d places\n%s",
                        room.getType_salle(),
                        room.getCapacite(),
                        room.getStatus())
        );
        details.setStyle("-fx-text-fill: #6c757d; -fx-font-size: 12px; -fx-text-alignment: center;");

        card.getChildren().addAll(imageView, title, details);
        return card;
    }

    private void loadDepartmentImage(ImageView imageView, String imageName) {
        try {
            InputStream is = getClass().getResourceAsStream("/images/" + imageName);
            if (is != null) {
                imageView.setImage(new Image(is, 270, 150, true, true));
                return;
            }
            InputStream defaultIs = getClass().getResourceAsStream("/images/default_dept.png");
            if (defaultIs != null) {
                imageView.setImage(new Image(defaultIs, 270, 150, true, true));
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void loadRoomImage(ImageView imageView, String imageName) {
        try {
            InputStream is = getClass().getResourceAsStream("/images/" + imageName);
            if (is != null) {
                imageView.setImage(new Image(is, 120, 80, true, true));
                return;
            }
            InputStream defaultIs = getClass().getResourceAsStream("/images/default_room.png");
            if (defaultIs != null) {
                imageView.setImage(new Image(defaultIs, 120, 80, true, true));
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void searchDepartments(String searchTerm) {
        departementContainer.getChildren().clear();
        List<departement> results = (searchTerm == null || searchTerm.isEmpty())
                ? departementService.getAllDepartements()
                : departementService.searchDepartements(searchTerm);
        for (departement dept : results) {
            departementContainer.getChildren().add(createDepartmentCard(dept));
        }
 }


    @FXML
    private void handleBackButton() {
        try {
            Stage stage = (Stage) backButton.getScene().getWindow();
            Parent root = FXMLLoader.load(getClass().getResource("/front.fxml"));
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.show();
        } catch (Exception e) {
            e.printStackTrace();
            showAlert("Error", "Could not load the dashboard");
        }
    }
    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}