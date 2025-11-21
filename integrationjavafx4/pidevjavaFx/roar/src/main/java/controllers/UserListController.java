package controllers;

import entite.Users;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.chart.BarChart;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import service.UserService;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;
import java.io.IOException;
import java.sql.SQLException;
import java.util.List;
import java.util.stream.Collectors;

public class UserListController {

    //@ public invariant VBoxId != null;
    //@ public invariant searchInput != null;
    //@ public invariant roleFilter != null;
    //@ public invariant statsChart != null;
    //@ public invariant userService != null;
    //@ public invariant allUsers != null;
    //@ public invariant (\forall int i; 0 <= i && i < allUsers.size(); allUsers.get(i) != null);

    @FXML
    private VBox VBoxId;

    @FXML
    private TextField searchInput;

    @FXML
    private ComboBox<String> roleFilter;

    @FXML
    private HBox statsContainer;

    @FXML
    private BarChart<String, Number> statsChart;

    private final UserService userService = new UserService();

    private ObservableList<Users> allUsers = FXCollections.observableArrayList();

    /*@ public normal_behavior
    @   requires VBoxId != null && searchInput != null && roleFilter != null && statsChart != null;
    @   assignable allUsers, VBoxId.getChildren(), statsChart.data, statsChart.titleProperty();
    @   ensures statsChart.getBarGap() == 5;
    @   ensures statsChart.getCategoryGap() == 20;
    @   ensures statsChart.isLegendVisible();
    @   ensures statsChart.isAnimated();
    @*/

    @FXML
    public void initialize() {
        // Charger les utilisateurs au démarrage
        chargerUtilisateurs();

        // Ajouter des écouteurs pour la recherche et le filtrage dynamiques
        searchInput.textProperty().addListener((obs, oldValue, newValue) -> filterUsers());
        roleFilter.valueProperty().addListener((obs, oldValue, newValue) -> filterUsers());

        // Initialiser le BarChart
        statsChart.setBarGap(5);
        statsChart.setCategoryGap(20);
        statsChart.setLegendVisible(true);
        statsChart.setAnimated(true);
    }

    /*@ public normal_behavior
    @   requires VBoxId.getScene() != null;
    @   requires VBoxId.getScene().getWindow() instanceof Stage;
    @   assignable \everything;
    @ also
    @ public exceptional_behavior
    @   signals (IOException e) true;
    @*/

    @FXML
    private void ajouterUtilisateur() {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/ajouter_utilisateur.fxml"));
            Parent root = loader.load();

            Stage stage = (Stage) VBoxId.getScene().getWindow();
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.setTitle("Ajouter un utilisateur");
            stage.show();
            // Recharger les utilisateurs après ajout
            chargerUtilisateurs();
        } catch (IOException e) {
            e.printStackTrace();
            System.err.println("❌ Impossible de charger la vue ajouter_utilisateur.fxml : " + e.getMessage());
        }
    }

    /*@ public normal_behavior
    @   requires VBoxId.getScene() != null;
    @   requires VBoxId.getScene().getWindow() instanceof Stage;
    @   assignable \everything;
    @ also
    @ public exceptional_behavior
    @   signals (IOException e) true;
    @*/

    @FXML
    private void deconnexion() {
        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("/front.fxml"));
            Parent root = loader.load();

            Stage stage = (Stage) VBoxId.getScene().getWindow();
            Scene scene = new Scene(root);
            stage.setScene(scene);
            stage.setTitle("Connexion");
            stage.show();
        } catch (IOException e) {
            e.printStackTrace();
            System.err.println("❌ Impossible de charger la vue front.fxml : " + e.getMessage());
        }
    }

    /*@ private normal_behavior
    @   requires userService != null;
    @   requires allUsers != null;
    @   assignable allUsers, VBoxId.getChildren(), statsChart.data, statsChart.titleProperty();
    @   signals (SQLException e) false;
    @*/

    private void chargerUtilisateurs() {
        try {
            List<Users> utilisateurs = userService.listerUtilisateurs();
            allUsers.setAll(utilisateurs);
            filterUsers();
            updateStats();
        } catch (SQLException e) {
            System.err.println("❌ Erreur lors du chargement des utilisateurs : " + e.getMessage());
            showErrorAlert("Erreur lors du chargement des utilisateurs : " + e.getMessage());
        }
    }

    /*@ private normal_behavior
    @   requires searchInput != null && roleFilter != null;
    @   requires allUsers != null && VBoxId != null && statsChart != null;
    @   assignable VBoxId.getChildren(), statsChart.data, statsChart.titleProperty();
    @*/

    private void filterUsers() {
        String searchText = searchInput.getText().toLowerCase();
        String selectedRole = roleFilter.getValue() != null ? roleFilter.getValue() : "";

        List<Users> filteredUsers = allUsers.stream()
                .filter(user -> {
                    // Filtre par nom ou prénom
                    boolean matchesSearch = searchText.isEmpty() ||
                            (user.getNom() != null && user.getNom().toLowerCase().contains(searchText)) ||
                            (user.getPrenom() != null && user.getPrenom().toLowerCase().contains(searchText));
                    // Filtre par rôle
                    boolean matchesRole = selectedRole.isEmpty() ||
                            (user.getRoles() != null && user.getRoles().contains(selectedRole));
                    return matchesSearch && matchesRole;
                })
                .collect(Collectors.toList());

        listUsersInVBox(filteredUsers);
        updateStats();
    }

    /*@ private normal_behavior
    @   requires statsChart != null && allUsers != null;
    @   assignable statsChart.data, statsChart.titleProperty();
    @   ensures statsChart.getData().size() == 1;
    @   ensures statsChart.getData().get(0).getName().equals("Utilisateurs");
    @   ensures allUsers.size() == 0 ==> statsChart.getTitle().equals("Aucun utilisateur trouvé");
    @   ensures allUsers.size() > 0 ==> statsChart.getTitle().contains("Répartition des utilisateurs par rôle");
    @*/

    private void updateStats() {
        long total = allUsers.size();
        long patients = allUsers.stream().filter(u -> u.getRoles() != null && u.getRoles().contains("ROLE_PATIENT")).count();
        long medecins = allUsers.stream().filter(u -> u.getRoles() != null && u.getRoles().contains("ROLE_MEDECIN")).count();
        long pharmaciens = allUsers.stream().filter(u -> u.getRoles() != null && u.getRoles().contains("ROLE_PHARMACIEN")).count();
        long staff = allUsers.stream().filter(u -> u.getRoles() != null && u.getRoles().contains("ROLE_STAFF")).count();

        XYChart.Series<String, Number> series = new XYChart.Series<>();
        series.setName("Utilisateurs");
        series.getData().add(new XYChart.Data<>("Patients", patients));
        series.getData().add(new XYChart.Data<>("Médecins", medecins));
        series.getData().add(new XYChart.Data<>("Pharmaciens", pharmaciens));
        series.getData().add(new XYChart.Data<>("Staff", staff));

        statsChart.getData().clear();
        statsChart.getData().add(series);

        // Appliquer des styles personnalisés aux barres
        String[] colors = {"#28a745", "#dc3545", "#ffc107", "#17a2b8"}; // Vert, Rouge, Jaune, Bleu
        int index = 0;
        for (XYChart.Data<String, Number> data : series.getData()) {
            if (data.getNode() != null) {
                data.getNode().setStyle("-fx-bar-fill: " + colors[index % colors.length] + ";");
            }
            index++;
        }

        // Mettre à jour le titre
        if (total == 0) {
            statsChart.setTitle("Aucun utilisateur trouvé");
        } else {
            statsChart.setTitle("Répartition des utilisateurs par rôle (Total: " + total + ")");
        }
    }

    /*@ private normal_behavior
    @   requires VBoxId != null && users != null;
    @   requires (\forall int i; 0 <= i && i < users.size(); users.get(i) != null);
    @   assignable VBoxId.getChildren();
    @   ensures VBoxId.getChildren().size() == users.size();
    @   ensures (\forall int i; 0 <= i && i < VBoxId.getChildren().size();
    @               VBoxId.getChildren().get(i) instanceof HBox);
    @*/

    private void listUsersInVBox(List<Users> users) {
        VBoxId.getChildren().clear();

        for (Users user : users) {
            HBox userBox = new HBox(20);
            userBox.setPadding(new Insets(10));
            userBox.setStyle("-fx-border-color: #ddd; -fx-border-radius: 8; -fx-background-radius: 8; -fx-background-color: #f9f9f9;");
            userBox.setAlignment(Pos.CENTER_LEFT);

            Label nomLabel = new Label("👤 " + (user.getNom() != null ? user.getNom() : ""));
            Label prenomLabel = new Label(user.getPrenom() != null ? user.getPrenom() : "");
            Label emailLabel = new Label("✉ " + (user.getEmail() != null ? user.getEmail() : ""));
            String rolesText = user.getRoles() != null ? String.join(", ", user.getRoles()) : "";
            Label roleLabel = new Label("🔑 " + rolesText);
            Label typeLabel = new Label("📌 " + (user.getType() != null ? user.getType() : ""));

            Button btnModifier = new Button("✏ Modifier");
            btnModifier.setStyle("-fx-background-color: #0d6efd; -fx-text-fill: white;");
            btnModifier.setOnAction(e -> {
                try {
                    FXMLLoader loader = new FXMLLoader(getClass().getResource("/ModifierUtilisateur.fxml"));
                    Parent root = loader.load();
                    ModifierUtilisateurController controller = loader.getController();
                    controller.setUtilisateur(user);
                    Stage stage = (Stage) btnModifier.getScene().getWindow();
                    stage.setScene(new Scene(root));
                    stage.setTitle("Modifier Utilisateur");
                    stage.show();
                    // Recharger les utilisateurs après modification
                    chargerUtilisateurs();
                } catch (IOException ex) {
                    System.err.println("❌ Impossible de charger la vue ModifierUtilisateur.fxml : " + ex.getMessage());
                }
            });

            Button btnSupprimer = new Button("🗑 Supprimer");
            btnSupprimer.setStyle("-fx-background-color: #dc3545; -fx-text-fill: white;");
            btnSupprimer.setOnAction(e -> {
                try {
                    userService.supprimer(user.getId());
                    chargerUtilisateurs();
                } catch (SQLException ex) {
                    System.err.println("❌ Échec de la suppression : " + ex.getMessage());
                }
            });

            Region spacer = new Region();
            HBox.setHgrow(spacer, Priority.ALWAYS);

            userBox.getChildren().addAll(nomLabel, prenomLabel, emailLabel, roleLabel, typeLabel, spacer, btnModifier, btnSupprimer);
            VBoxId.getChildren().add(userBox);
        }
    }

    /*@ private normal_behavior
    @   requires message != null;
    @   assignable \nothing;
    @*/

    private void showErrorAlert(String message) {
        Alert alert = new Alert(Alert.AlertType.ERROR);
        alert.setTitle("Erreur");
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}