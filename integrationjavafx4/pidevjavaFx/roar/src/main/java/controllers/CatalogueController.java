package controllers;

import entite.Medicament;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.geometry.Pos;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.effect.DropShadow;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.TilePane;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.scene.text.Text;
import javafx.stage.Stage;

import java.net.URL;
import java.time.LocalDate;
import java.util.Arrays;
import java.util.List;
import java.util.ResourceBundle;

public class CatalogueController implements Initializable {

    @FXML
    private TilePane tilePane;
    @FXML
    private Button backButton;

    @Override
    public void initialize(URL url, ResourceBundle resourceBundle) {
        // Exemple de données en dur (à remplacer par une récupération depuis la base de données)
        List<Medicament> medicaments = Arrays.asList(
                new Medicament("Paracétamol", "Soulage douleurs et fièvre", "Analgesique", 3.50, 50, LocalDate.now(), LocalDate.now().plusYears(1)),
                new Medicament("Ibuprofène", "Anti-inflammatoire courant", "Anti-inflammatoire", 5.00, 30, LocalDate.now(), LocalDate.now().plusYears(2)),
                new Medicament("Amoxicilline", "Antibiotique à large spectre", "Antibiotique", 8.75, 20, LocalDate.now(), LocalDate.now().plusYears(1)),
                new Medicament("Effiralgant", "Pour soulager les douleurs modérées", "Analgésique", 4.20, 40, LocalDate.now(), LocalDate.now().plusMonths(18)),
                new Medicament("Augmentin", "Antibiotique puissant à large spectre", "Antibiotique", 11.30, 25, LocalDate.now(), LocalDate.now().plusYears(2)),
                new Medicament("Smecta", "Contre les diarrhées et douleurs digestives", "Antidiarrhéique", 2.90, 60, LocalDate.now(), LocalDate.now().plusYears(1)),
                new Medicament("Avene", "Crème hydratante et apaisante", "Dermatologique", 15.00, 35, LocalDate.now(), LocalDate.now().plusMonths(8)),
                new Medicament("SVR", "Soins dermatologiques spécialisés", "Dermatologique", 17.50, 20, LocalDate.now(), LocalDate.now().plusMonths(10)),
                new Medicament("Tamizole", "Traitement des ulcères gastriques", "Anti-ulcéreux", 6.80, 22, LocalDate.now(), LocalDate.now().plusYears(1)),
                new Medicament("Tardyferon", "Supplément en fer pour l’anémie", "Complément", 4.50, 45, LocalDate.now(), LocalDate.now().plusYears(1)),
                new Medicament("Aspirine", "Fluidifiant sanguin et antidouleur", "Antiagrégant plaquettaire", 3.10, 55, LocalDate.now(), LocalDate.now().plusMonths(14))
        );

        for (Medicament m : medicaments) {
            tilePane.getChildren().add(createMedicamentCard(m));
        }
    }

    private VBox createMedicamentCard(Medicament medicament) {
        ImageView imageView;
        try {
            String imagePath = getImagePathForMedicament(medicament);
            URL imageUrl = getClass().getResource(imagePath);
            if (imageUrl != null) {
                imageView = new ImageView(new Image(imageUrl.toExternalForm()));
            } else {
                System.err.println("Image not found for: " + medicament.getNom_medicament());
                imageView = new ImageView(new Image(getClass().getResource("/img/default.png").toExternalForm()));
            }
        } catch (Exception e) {
            imageView = new ImageView(new Image(getClass().getResource("/img/default.png").toExternalForm()));
        }

        imageView.setFitWidth(200);
        imageView.setFitHeight(200);
        imageView.setPreserveRatio(true);
        imageView.setSmooth(true);
        imageView.setEffect(new DropShadow(10, Color.GRAY));

        Label name = new Label(medicament.getNom_medicament());
        name.setStyle("-fx-font-size: 18px; -fx-font-weight: bold;");

        Text desc = new Text(medicament.getDescription_medicament());
        desc.setWrappingWidth(200);
        desc.setStyle("-fx-font-size: 13px;");

        Label prix = new Label(String.format("%.2f TND", medicament.getPrix_medicament()));
        prix.setTextFill(Color.DARKGREEN);
        prix.setStyle("-fx-font-weight: bold; -fx-font-size: 14px;");

        VBox card = new VBox(imageView, name, desc, prix);
        card.setSpacing(12);
        card.setAlignment(Pos.CENTER);
        card.setStyle("""
        -fx-background-color: #ffffff;
        -fx-border-radius: 12px;
        -fx-background-radius: 12px;
        -fx-padding: 15;
        -fx-effect: dropshadow(two-pass-box, rgba(0,0,0,0.1), 10, 0.1, 0, 5);
        """);

        card.setPrefWidth(220);
        card.setPrefHeight(360);

        return card;
    }


    // Méthode pour construire dynamiquement le chemin d'image à partir du nom
    private String getImagePathForMedicament(Medicament medicament) {
        String nom = medicament.getNom_medicament()
                .toLowerCase()
                .replace("é", "e")
                .replace("è", "e")
                .replace("à", "a")
                .replace("ê", "e")
                .replaceAll("[^a-z0-9]", ""); // Supprime accents et caractères spéciaux

        return "/img/" + nom + ".png";
    }
    @FXML
    private void goToCommande() {
        try {
            javafx.fxml.FXMLLoader loader = new javafx.fxml.FXMLLoader(getClass().getResource("/commande.fxml"));
            javafx.scene.Parent root = loader.load();
            tilePane.getScene().setRoot(root);  // Remplace la scène actuelle
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    @FXML
    private void handleBackButtoncatalogue() {
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

