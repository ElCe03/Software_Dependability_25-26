package controllers;

import entite.departement;
import javafx.fxml.FXML;
import javafx.scene.control.TextField;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.stage.FileChooser;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;

public class EditDepartementController {
    /*@
      @ private invariant IMAGE_DIR != null;
      @*/
    @FXML private TextField nomField;
    @FXML private TextField adresseField;
    @FXML private TextField imageField;
    @FXML private ImageView imagePreview;

    private departement departement;
    private String imagePath;
    private static final String IMAGE_DIR = "src/main/resources/images/";

    @FXML
    public void initialize() {
        // Initialisation si nécessaire
    }
    /*@ public normal_behavior
          @   requires departement != null;
          @   requires nomField != null;
          @   requires adresseField != null;
          @   requires imageField != null;
          @   assignable this.departement, this.imagePath,
          @              nomField.text, adresseField.text, imageField.text,
          @              imagePreview.image;
          @   ensures this.departement == departement;
          @   ensures nomField.getText().equals(departement.getNom());
          @   ensures adresseField.getText().equals(departement.getAdresse());
          @   ensures this.imagePath == departement.getImage();
          @*/
    public void setDepartementData(departement departement) {
        this.departement = departement;
        nomField.setText(departement.getNom());
        adresseField.setText(departement.getAdresse());
        imageField.setText(departement.getImage());
        this.imagePath = departement.getImage();

        if (departement.getImage() != null && !departement.getImage().isEmpty()) {
            File imageFile = new File(IMAGE_DIR + departement.getImage());
            if (imageFile.exists()) {
                imagePreview.setImage(new Image(imageFile.toURI().toString()));
            }
        }
    }
    /*@ private normal_behavior
          @   requires imageField != null && imagePreview != null;
          @   assignable imagePath, imageField.text, imagePreview.image;
          @*/
    @FXML
    private void handleBrowseImage() {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Choisir une image");
        fileChooser.getExtensionFilters().addAll(
                new FileChooser.ExtensionFilter("Images", "*.png", "*.jpg", "*.jpeg", "*.gif")
        );

        File selectedFile = fileChooser.showOpenDialog(null);
        if (selectedFile != null) {
            try {
                String fileName = System.currentTimeMillis() + "_" + selectedFile.getName();
                File destFile = new File(IMAGE_DIR + fileName);
                Files.copy(selectedFile.toPath(), destFile.toPath(), StandardCopyOption.REPLACE_EXISTING);

                imagePath = fileName;
                imageField.setText(fileName);
                imagePreview.setImage(new Image(destFile.toURI().toString()));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    /*@ public normal_behavior
          @   requires this.departement != null;
          @   requires nomField != null && adresseField != null;
          @   assignable departement.nom, departement.adresse, departement.image;
          @   ensures \result != null;
          @   ensures \result == this.departement;
          @   ensures \result.getNom().equals(nomField.getText());
          @   ensures \result.getAdresse().equals(adresseField.getText());
          @   ensures \result.getImage() == this.imagePath;
          @*/
    public departement getUpdatedDepartement() {
        departement.setNom(nomField.getText());
        departement.setAdresse(adresseField.getText());
        departement.setImage(imagePath);
        return departement;
    }
}