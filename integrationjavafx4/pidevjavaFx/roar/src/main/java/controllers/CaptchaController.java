package controllers;
import javafx.fxml.FXML;
import javafx.scene.control.TextField;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.control.Alert;
import entite.CaptchaGenerator;

import java.io.File;
import java.io.IOException;

public class CaptchaController {
    @FXML
    private ImageView captchaImageView;
    @FXML
    private TextField captchaInputField;
    //@ private invariant correctCaptcha == null || correctCaptcha.length() > 0;
    private String correctCaptcha;
    /*@ public normal_behavior
          @   requires captchaImageView != null;
          @   assignable correctCaptcha, captchaImageView.imageProperty();
          @   ensures correctCaptcha != null && correctCaptcha.length() > 0;
          @   ensures captchaImageView.getImage() != null;
          @*/
    @FXML
    public void initialize() {
        generateNewCaptcha();
    }

    /*@ public normal_behavior
      @   requires captchaImageView != null;
      @   assignable correctCaptcha, captchaImageView.imageProperty();
      @   ensures correctCaptcha != null && correctCaptcha.length() > 0;
      @   ensures captchaImageView.getImage() != null;
      @*/
    public void generateNewCaptcha() {
        try {
            correctCaptcha = CaptchaGenerator.generateCaptchaText();
            File captchaFile = CaptchaGenerator.generateCaptchaImage(correctCaptcha);
            captchaImageView.setImage(new Image(captchaFile.toURI().toString()));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    /*@ public normal_behavior
          @   requires captchaInputField != null;
          @   requires captchaImageView != null;
          @   requires correctCaptcha != null;
          @   assignable captchaInputField.textProperty(),
          @              correctCaptcha,
          @              captchaImageView.imageProperty();
          @   ensures captchaInputField.getText().isEmpty();
          @   ensures !\old(captchaInputField.getText().trim().equals(correctCaptcha)) ==>
          @           (correctCaptcha != \old(correctCaptcha));
          @*/
    @FXML
    public void verifyCaptcha() {
        String userInput = captchaInputField.getText().trim();
        if (userInput.equals(correctCaptcha)) {
            showAlert("Succès", "Captcha correct !");
        } else {
            showAlert("Erreur", "Captcha incorrect. Réessayez !");
            generateNewCaptcha(); // Générer un nouveau captcha après une mauvaise réponse
        }
        captchaInputField.clear();
    }
    /*@ private normal_behavior
          @   requires title != null;
          @   requires message != null;
          @   assignable \nothing;
          @*/
    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}

