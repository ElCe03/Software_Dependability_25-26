package controllers;

import entite.Service;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.text.Font;
import javafx.scene.text.FontWeight;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import service.serviceservice;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import javafx.event.ActionEvent;
import javafx.scene.Node;
import java.io.IOException;

public class ServiceListController {
    @FXML private VBox galleryContainer;
    @FXML private FlowPane servicesFlowPane;
    @FXML private TextField searchField;
    @FXML private Button refreshBtn;
    @FXML private Button backBtn;
    @FXML private ComboBox<String> languageComboBox;
    @FXML private ProgressIndicator loadingIndicator;
    @FXML private Label translationWarningLabel;

    private serviceservice serviceService = new serviceservice();
    private String currentLanguage = "en";
    private boolean translationFailed = false;

    @FXML
    public void initialize() {
        applyStyles();
        setupLanguageSelector();
        loadServices();
        setupSearch();
        setupBackButton();
        if (loadingIndicator != null) {
            loadingIndicator.setVisible(false);
        }
        if (translationWarningLabel != null) {
            translationWarningLabel.setVisible(false);
        }
    }

    private void setupLanguageSelector() {
        languageComboBox.getItems().addAll("English", "French", "Spanish", "German", "Arabic");
        languageComboBox.setValue("English");

        languageComboBox.setOnAction(e -> {
            String selected = languageComboBox.getValue();
            switch (selected) {
                case "English": currentLanguage = "en"; break;
                case "French": currentLanguage = "fr"; break;
                case "Spanish": currentLanguage = "es"; break;
                case "German": currentLanguage = "de"; break;
                case "Arabic": currentLanguage = "ar"; break;
            }
            translationFailed = false;
            Translator.resetFailures();
            loadServices();
        });

        languageComboBox.setStyle(
                "-fx-background-color: white; " +
                        "-fx-border-color: #e2e8f0; " +
                        "-fx-border-radius: 20; " +
                        "-fx-background-radius: 20; " +
                        "-fx-padding: 5 15;"
        );
    }

    private void applyStyles() {
        galleryContainer.setStyle("-fx-background-color: #f8fafc;");

        searchField.setStyle(
                "-fx-pref-width: 300px; " +
                        "-fx-pref-height: 40px; " +
                        "-fx-font-size: 14px; " +
                        "-fx-background-radius: 20; " +
                        "-fx-border-radius: 20; " +
                        "-fx-border-color: #e2e8f0; " +
                        "-fx-padding: 5 15;"
        );

        refreshBtn.setStyle(
                "-fx-background-color: #3b82f6; " +
                        "-fx-text-fill: white; " +
                        "-fx-font-weight: bold; " +
                        "-fx-font-size: 14px; " +
                        "-fx-padding: 8 20; " +
                        "-fx-background-radius: 20;"
        );

        backBtn.setStyle(
                "-fx-background-color: #94a3b8; " +
                        "-fx-text-fill: white; " +
                        "-fx-font-weight: bold; " +
                        "-fx-font-size: 14px; " +
                        "-fx-padding: 8 20; " +
                        "-fx-background-radius: 20;"
        );

        backBtn.setOnMouseEntered(e -> backBtn.setStyle(
                "-fx-background-color: #64748b; " +
                        "-fx-text-fill: white; " +
                        "-fx-font-weight: bold; " +
                        "-fx-font-size: 14px; " +
                        "-fx-padding: 8 20; " +
                        "-fx-background-radius: 20;"
        ));
        backBtn.setOnMouseExited(e -> backBtn.setStyle(
                "-fx-background-color: #94a3b8; " +
                        "-fx-text-fill: white; " +
                        "-fx-font-weight: bold; " +
                        "-fx-font-size: 14px; " +
                        "-fx-padding: 8 20; " +
                        "-fx-background-radius: 20;"
        ));
    }

    private CompletableFuture<String> translateText(String text) {
        if (text == null || text.isEmpty() || "en".equals(currentLanguage)) {
            return CompletableFuture.completedFuture(text);
        }

        // First try the fallback
        String fallback = TranslatorFallback.translate(text, currentLanguage);
        if (!fallback.equals(text)) {
            return CompletableFuture.completedFuture(fallback);
        }

        // Only use API for dynamic text
        return Translator.translateAsync(text, "en", currentLanguage)
                .orTimeout(2, TimeUnit.SECONDS)
                .exceptionally(throwable -> {
                    translationFailed = true;
                    return text; // Return original if translation fails
                });
    }

    private void setupBackButton() {
        backBtn.setOnAction(e -> {
            try {
                Parent root = FXMLLoader.load(getClass().getResource("/front.fxml"));
                Stage stage = (Stage) backBtn.getScene().getWindow();
                stage.setScene(new Scene(root));
                stage.show();
            } catch (Exception ex) {
                ex.printStackTrace();
                showAlert("Navigation Error", "Failed to load the front page.", Alert.AlertType.ERROR);
            }
        });
    }

    private void showAlert(String title, String message, Alert.AlertType type) {
        Platform.runLater(() -> {
            Alert alert = new Alert(type);
            alert.setTitle(title);
            alert.setHeaderText(null);
            alert.setContentText(message);
            alert.showAndWait();
        });
    }

    private ImageView createLogoView(double size) {
        try {
            Image logoImage = new Image(getClass().getResourceAsStream("/img/logo.png"));
            ImageView logoView = new ImageView(logoImage);
            logoView.setFitHeight(size);
            logoView.setFitWidth(size);
            logoView.setPreserveRatio(true);
            logoView.setSmooth(true);
            logoView.setCache(true);
            return logoView;
        } catch (Exception e) {
            return null;
        }
    }

    private StackPane createLogoPlaceholder(Service service, double size) {
        StackPane placeholder = new StackPane();
        placeholder.setMinSize(size, size);
        placeholder.setStyle("-fx-background-color: #3b82f6; -fx-background-radius: " + (size/2) + ";");

        Text initial = new Text(service.getName().substring(0, 1).toUpperCase());
        initial.setFont(Font.font("Arial", FontWeight.BOLD, size/2));
        initial.setFill(Color.WHITE);
        placeholder.getChildren().add(initial);
        return placeholder;
    }

    private StackPane createImagePlaceholder(Service service, double width, double height) {
        StackPane placeholder = new StackPane();
        placeholder.setMinSize(width, height);
        placeholder.setStyle("-fx-background-color: #e2e8f0; -fx-background-radius: 8;");

        Text initial = new Text(service.getName().substring(0, 1).toUpperCase());
        initial.setFont(Font.font("Arial", FontWeight.BOLD, Math.min(width, height)/2));
        initial.setFill(Color.web("#94a3b8"));
        placeholder.getChildren().add(initial);
        return placeholder;
    }

    private void loadServices() {
        if (loadingIndicator != null) {
            loadingIndicator.setVisible(true);
        }

        translationFailed = false;
        Translator.resetFailures();

        servicesFlowPane.getChildren().clear();
        List<Service> services = serviceService.getAllServices();

        servicesFlowPane.setHgap(25);
        servicesFlowPane.setVgap(25);
        servicesFlowPane.setPadding(new Insets(20));
        servicesFlowPane.setPrefWrapLength(1000);

        List<CompletableFuture<Void>> futures = new ArrayList<>();
        for (Service service : services) {
            CompletableFuture<Void> future = createServiceCardAsync(service)
                    .thenAcceptAsync(card -> servicesFlowPane.getChildren().add(card), Platform::runLater);
            futures.add(future);
        }

        CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]))
                .orTimeout(10, TimeUnit.SECONDS)
                .whenComplete((result, throwable) -> Platform.runLater(() -> {
                    if (loadingIndicator != null) {
                        loadingIndicator.setVisible(false);
                    }
                    if (translationWarningLabel != null) {
                        translationWarningLabel.setVisible(translationFailed);
                        if (translationFailed) {
                            translationWarningLabel.setText(
                                    TranslatorFallback.translate(
                                            "Translation unavailable, using English.",
                                            currentLanguage
                                    )
                            );
                        }
                    }
                    if (throwable != null) {
                        showAlert(
                                "Loading Error",
                                "Failed to load services in time.",
                                Alert.AlertType.WARNING
                        );
                    }
                }));
    }

    private CompletableFuture<VBox> createServiceCardAsync(Service service) {
        VBox card = new VBox();
        card.setAlignment(Pos.TOP_CENTER);
        card.setSpacing(15);
        card.setPadding(new Insets(20));
        card.setMinWidth(300);
        card.setMaxWidth(300);
        card.setStyle(
                "-fx-background-color: white; " +
                        "-fx-background-radius: 12; " +
                        "-fx-border-radius: 12; " +
                        "-fx-border-color: #e2e8f0; " +
                        "-fx-effect: dropshadow(three-pass-box, rgba(0,0,0,0.08), 10, 0, 0, 2);" +
                        "-fx-cursor: hand;"
        );

        card.setOnMouseEntered(e -> card.setStyle(
                "-fx-background-color: #f9fafb; " +
                        "-fx-border-color: #3b82f6; " +
                        "-fx-effect: dropshadow(three-pass-box, rgba(59,130,246,0.15), 12, 0, 0, 4);"
        ));
        card.setOnMouseExited(e -> card.setStyle(
                "-fx-background-color: white; " +
                        "-fx-border-color: #e2e8f0; " +
                        "-fx-effect: dropshadow(three-pass-box, rgba(0,0,0,0.08), 10, 0, 0, 2);"
        ));

        HBox headerBox = new HBox(12);
        headerBox.setAlignment(Pos.CENTER_LEFT);

        ImageView logoView = createLogoView(40);
        if (logoView != null) {
            headerBox.getChildren().add(logoView);
        } else {
            headerBox.getChildren().add(createLogoPlaceholder(service, 40));
        }

        CompletableFuture<String> nameFuture = translateText(service.getName());
        CompletableFuture<String> descFuture = translateText(service.getDescription());
        CompletableFuture<String> buttonTextFuture = translateText("See Service Details");
        CompletableFuture<String> durationTextFuture = translateText("⏱ %d minutes");

        return CompletableFuture.allOf(nameFuture, descFuture, buttonTextFuture, durationTextFuture)
                .thenApplyAsync(v -> {
                    try {
                        String translatedName = nameFuture.get();
                        Label titleLabel = new Label(translatedName);
                        titleLabel.setFont(Font.font("Segoe UI", FontWeight.BOLD, 18));
                        titleLabel.setTextFill(Color.web("#1e293b"));
                        titleLabel.setWrapText(true);
                        titleLabel.setMaxWidth(220);
                        headerBox.getChildren().add(titleLabel);
                        card.getChildren().add(headerBox);

                        StackPane imageContainer = new StackPane();
                        imageContainer.setStyle("-fx-background-color: #f1f5f9; -fx-background-radius: 8;");

                        try {
                            ImageView imageView = new ImageView(new Image(getClass().getResourceAsStream("/img/logo.png")));
                            imageView.setFitWidth(260);
                            imageView.setFitHeight(160);
                            imageView.setPreserveRatio(true);
                            imageView.setSmooth(true);
                            imageView.setCache(true);
                            imageContainer.getChildren().add(imageView);
                        } catch (Exception e) {
                            imageContainer.getChildren().add(createImagePlaceholder(service, 260, 160));
                        }
                        card.getChildren().add(imageContainer);

                        HBox durationBox = new HBox(5);
                        durationBox.setAlignment(Pos.CENTER_LEFT);
                        String durationText = String.format(durationTextFuture.get(), service.getDuration());
                        Label durationLabel = new Label(durationText);
                        durationLabel.setFont(Font.font("Segoe UI", FontWeight.NORMAL, 14));
                        durationLabel.setTextFill(Color.web("#64748b"));
                        durationBox.getChildren().add(durationLabel);
                        card.getChildren().add(durationBox);

                        String translatedDesc = descFuture.get();
                        String shortDesc = translatedDesc.length() > 100 ?
                                translatedDesc.substring(0, 100) + "..." : translatedDesc;
                        Label descLabel = new Label(shortDesc);
                        descLabel.setFont(Font.font("Segoe UI", FontWeight.NORMAL, 13));
                        descLabel.setTextFill(Color.web("#475569"));
                        descLabel.setWrapText(true);
                        card.getChildren().add(descLabel);

                        String buttonText = buttonTextFuture.get();
                        Button detailsBtn = new Button(buttonText);
                        detailsBtn.setStyle(
                                "-fx-background-color: #3b82f6; " +
                                        "-fx-text-fill: white; " +
                                        "-fx-font-weight: bold; " +
                                        "-fx-font-size: 13px; " +
                                        "-fx-padding: 8 15; " +
                                        "-fx-background-radius: 20;"
                        );

                        detailsBtn.setOnMouseEntered(e -> detailsBtn.setStyle(
                                "-fx-background-color: #2563eb; " +
                                        "-fx-text-fill: white; " +
                                        "-fx-font-weight: bold; " +
                                        "-fx-font-size: 13px; " +
                                        "-fx-padding: 8 15; " +
                                        "-fx-background-radius: 20;"
                        ));
                        detailsBtn.setOnMouseExited(e -> detailsBtn.setStyle(
                                "-fx-background-color: #3b82f6; " +
                                        "-fx-text-fill: white; " +
                                        "-fx-font-weight: bold; " +
                                        "-fx-font-size: 13px; " +
                                        "-fx-padding: 8 15; " +
                                        "-fx-background-radius: 20;"
                        ));

                        detailsBtn.setOnAction(e -> showServiceDetails(service));
                        card.getChildren().add(detailsBtn);

                        return card;
                    } catch (Exception e) {
                        System.err.println("Error creating service card: " + e.getMessage());
                        return card;
                    }
                }, Platform::runLater);
    }

    private void showServiceDetails(Service service) {
        Dialog<Void> dialog = new Dialog<>();
        dialog.initOwner(servicesFlowPane.getScene().getWindow());

        CompletableFuture<String> dialogTitleFuture = translateText("Service Details - %s")
                .thenApply(t -> String.format(t, service.getName()));

        CompletableFuture<String> closeButtonTextFuture = translateText("Close");
        CompletableFuture<String> durationTitleFuture = translateText("Duration:");
        CompletableFuture<String> durationValueFuture = translateText("%d minutes")
                .thenApply(t -> String.format(t, service.getDuration()));
        CompletableFuture<String> descTitleFuture = translateText("Description:");
        CompletableFuture<String> descValueFuture = translateText(service.getDescription());

        CompletableFuture.allOf(
                dialogTitleFuture, closeButtonTextFuture,
                durationTitleFuture, durationValueFuture,
                descTitleFuture, descValueFuture
        ).thenAcceptAsync(v -> {
            try {
                dialog.setTitle(dialogTitleFuture.get());

                ButtonType closeButtonType = new ButtonType(closeButtonTextFuture.get(),
                        ButtonBar.ButtonData.CANCEL_CLOSE);
                dialog.getDialogPane().getButtonTypes().add(closeButtonType);

                DialogPane dialogPane = dialog.getDialogPane();
                dialogPane.setStyle(
                        "-fx-background-color: white; " +
                                "-fx-border-color: #e2e8f0; " +
                                "-fx-border-width: 1px; " +
                                "-fx-border-radius: 12; " +
                                "-fx-background-radius: 12; " +
                                "-fx-effect: dropshadow(three-pass-box, rgba(0,0,0,0.1), 15, 0, 0, 0);"
                );
                dialogPane.setMinWidth(600);

                VBox content = new VBox(20);
                content.setPadding(new Insets(25));
                content.setAlignment(Pos.TOP_CENTER);

                HBox headerBox = new HBox(15);
                headerBox.setAlignment(Pos.CENTER_LEFT);

                ImageView logoView = createLogoView(50);
                if (logoView != null) {
                    headerBox.getChildren().add(logoView);
                } else {
                    headerBox.getChildren().add(createLogoPlaceholder(service, 50));
                }

                Label titleLabel = new Label(service.getName());
                titleLabel.setFont(Font.font("Segoe UI", FontWeight.BOLD, 24));
                titleLabel.setTextFill(Color.web("#1e293b"));
                headerBox.getChildren().add(titleLabel);
                content.getChildren().add(headerBox);

                StackPane imageContainer = new StackPane();
                imageContainer.setStyle("-fx-background-color: #f1f5f9; -fx-background-radius: 10;");

                try {
                    ImageView imageView = new ImageView(new Image(getClass().getResourceAsStream("/img/blog1.jpg")));
                    imageView.setFitWidth(500);
                    imageView.setFitHeight(280);
                    imageView.setPreserveRatio(true);
                    imageView.setSmooth(true);
                    imageView.setCache(true);
                    imageContainer.getChildren().add(imageView);
                } catch (Exception e) {
                    imageContainer.getChildren().add(createImagePlaceholder(service, 500, 280));
                }
                content.getChildren().add(imageContainer);

                GridPane detailsGrid = new GridPane();
                detailsGrid.setHgap(20);
                detailsGrid.setVgap(15);
                detailsGrid.setPadding(new Insets(20, 0, 0, 0));

                Label durationTitle = new Label(durationTitleFuture.get());
                durationTitle.setFont(Font.font("Segoe UI", FontWeight.BOLD, 16));
                durationTitle.setTextFill(Color.web("#475569"));

                Label durationValue = new Label(durationValueFuture.get());
                durationValue.setFont(Font.font("Segoe UI", FontWeight.NORMAL, 16));
                durationValue.setTextFill(Color.web("#334155"));

                detailsGrid.addRow(0, durationTitle, durationValue);

                Label descTitle = new Label(descTitleFuture.get());
                descTitle.setFont(Font.font("Segoe UI", FontWeight.BOLD, 16));
                descTitle.setTextFill(Color.web("#475569"));

                Label descValue = new Label(descValueFuture.get());
                descValue.setFont(Font.font("Segoe UI", FontWeight.NORMAL, 15));
                descValue.setTextFill(Color.web("#334155"));
                descValue.setWrapText(true);
                descValue.setMaxWidth(450);

                detailsGrid.addRow(1, descTitle, descValue);
                content.getChildren().add(detailsGrid);

                dialogPane.setContent(content);
                dialog.showAndWait();
            } catch (Exception e) {
                System.err.println("Error showing service details: " + e.getMessage());
            }
        }, Platform::runLater);
    }

    private void setupSearch() {
        searchField.textProperty().addListener((observable, oldValue, newValue) -> {
            servicesFlowPane.getChildren().clear();
            List<Service> services = serviceService.getAllServices();

            List<CompletableFuture<Void>> futures = new ArrayList<>();
            for (Service service : services) {
                if (newValue == null || newValue.isEmpty() ||
                        service.getName().toLowerCase().contains(newValue.toLowerCase()) ||
                        service.getDescription().toLowerCase().contains(newValue.toLowerCase())) {
                    CompletableFuture<Void> future = createServiceCardAsync(service)
                            .thenAcceptAsync(card -> servicesFlowPane.getChildren().add(card), Platform::runLater);
                    futures.add(future);
                }
            }

            CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]));
        });
    }

    @FXML
    private void handleRefresh() {
        loadServices();
    }



    @FXML
    private void goToPreScreen(ActionEvent event) {
        try {
            // Load the pre.fxml file
            Parent root = FXMLLoader.load(getClass().getResource("/pre.fxml"));

            // Get the current stage
            Stage stage = (Stage)((Node)event.getSource()).getScene().getWindow();

            // Create new scene
            Scene scene = new Scene(root);

            // Set the new scene
            stage.setScene(scene);
            stage.show();

        } catch (IOException e) {
            System.err.println("Error loading pre.fxml: " + e.getMessage());
            e.printStackTrace();

            // Show error alert
            Alert alert = new Alert(Alert.AlertType.ERROR);
            alert.setTitle("Navigation Error");
            alert.setHeaderText(null);
            alert.setContentText("Could not load the previous screen.");
            alert.showAndWait();
        }
    }



}