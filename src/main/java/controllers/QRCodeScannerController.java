package controllers;

import com.google.zxing.BinaryBitmap;
import com.google.zxing.MultiFormatReader;
import com.google.zxing.NotFoundException;
import com.google.zxing.Result;
import com.google.zxing.client.j2se.BufferedImageLuminanceSource;
import com.google.zxing.common.HybridBinarizer;
import entite.DossierMedicale;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import org.json.JSONObject;
import service.DossierMedicaleService;
import service.UserService;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Controller for scanning QR codes to view patient dosser information
 */
public class QRCodeScannerController implements Initializable {

    @FXML private Button btnBrowseQRCode;
    @FXML private TextField txtQRCodePath;
    @FXML private Button btnScanQRCode;
    @FXML private VBox patientInfoContainer;
    @FXML private Label lblPatientName;
    @FXML private Label lblDossierId;
    @FXML private Label lblDateCreation;
    @FXML private Label lblMedecinName;
    @FXML private Label lblStatus;
    @FXML private TextArea txtDossierDetails;
    
    private final DossierMedicaleService dossierService = new DossierMedicaleService();
    private final UserService userService = new UserService();
    
    private static final Logger logger = Logger.getLogger(QRCodeScannerController.class.getName());
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {

        patientInfoContainer.setVisible(false);
        patientInfoContainer.setManaged(false);
    }
    
    /**
     * Handle browse button click to select QR code image
     */
    @FXML
    private void handleBrowseQRCode(ActionEvent event) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Sélectionner une image de code QR");
        fileChooser.getExtensionFilters().addAll(
            new FileChooser.ExtensionFilter("Images", "*.png", "*.jpg", "*.jpeg")
        );
        
        Stage stage = (Stage) btnBrowseQRCode.getScene().getWindow();
        File selectedFile = fileChooser.showOpenDialog(stage);
        
        if (selectedFile != null) {
            txtQRCodePath.setText(selectedFile.getAbsolutePath());
        }
    }
    
    /**
     * Handle scan button click to decode QR code and display patient information
     */
    @FXML
    private void handleScanQRCode(ActionEvent event) {
        String filePath = txtQRCodePath.getText();
        if (filePath == null || filePath.isEmpty()) {
            showError("Veuillez sélectionner une image de code QR");
            return;
        }
        
        try {

            File qrCodeFile = new File(filePath);
            BufferedImage bufferedImage = ImageIO.read(qrCodeFile);
            
            if (bufferedImage == null) {
                showError("Impossible de lire l'image sélectionnée");
                return;
            }
            

            BinaryBitmap binaryBitmap = new BinaryBitmap(
                new HybridBinarizer(
                    new BufferedImageLuminanceSource(bufferedImage)
                )
            );
            
            Result result = new MultiFormatReader().decode(binaryBitmap);
            String decodedText = result.getText();
            

            processQRCodeData(decodedText);
            
        } catch (NotFoundException e) {
            showError("Aucun code QR détecté dans l'image");
            logger.log(Level.WARNING, "QR code not found in image", e);
        } catch (IOException e) {
            showError("Erreur lors de la lecture de l'image: " + e.getMessage());
            logger.log(Level.SEVERE, "Error reading image", e);
        } catch (Exception e) {
            showError("Erreur inattendue: " + e.getMessage());
            logger.log(Level.SEVERE, "Unexpected error processing QR code", e);
        }
    }
    
    /**
     * Process the decoded QR code data and display dossier information
     */
    private void processQRCodeData(String jsonData) {
        try {

            JSONObject dossierData = new JSONObject(jsonData);
            

            int dossierId = dossierData.getInt("id");
            String patientName = dossierData.getString("patient");
            String dateCreation = dossierData.getString("dateCreation");
            String statutDossier = dossierData.optString("statutDossier", "Non spécifié");
            String medecinName = dossierData.optString("medecin", "Non assigné");
            

            lblPatientName.setText(patientName);
            lblDossierId.setText(String.valueOf(dossierId));
            lblDateCreation.setText(dateCreation);
            lblStatus.setText(statutDossier);
            lblMedecinName.setText(medecinName);
            

            DossierMedicale dossier = dossierService.recupererDossierParId(dossierId);
            
            if (dossier != null) {

                StringBuilder details = new StringBuilder();
                details.append("HISTORIQUE DES MALADIES\n");
                details.append("------------------------\n");
                details.append(dossier.getHistoriqueDesMaladies() != null ? 
                        dossier.getHistoriqueDesMaladies() : "Aucun historique enregistré");
                details.append("\n\n");
                
                details.append("OPÉRATIONS PASSÉES\n");
                details.append("------------------\n");
                details.append(dossier.getOperationsPassees() != null ? 
                        dossier.getOperationsPassees() : "Aucune opération enregistrée");
                details.append("\n\n");
                
                details.append("CONSULTATIONS PASSÉES\n");
                details.append("---------------------\n");
                details.append(dossier.getConsultationsPassees() != null ? 
                        dossier.getConsultationsPassees() : "Aucune consultation enregistrée");
                details.append("\n\n");
                
                details.append("NOTES\n");
                details.append("-----\n");
                details.append(dossier.getNotes() != null ? 
                        dossier.getNotes() : "Aucune note enregistrée");
                

                txtDossierDetails.setText(details.toString());
            } else {

                txtDossierDetails.setText("Impossible de récupérer les détails complets du dossier dans la base de données.\n" +
                        "Le dossier a peut-être été supprimé ou le code QR est obsolète.");
            }
            

            patientInfoContainer.setVisible(true);
            patientInfoContainer.setManaged(true);
            
        } catch (Exception e) {
            showError("Format de données QR code invalide: " + e.getMessage());
            logger.log(Level.SEVERE, "Error processing QR code data", e);
        }
    }
    
    /**
     * Show error message
     */
    private void showError(String message) {

        patientInfoContainer.setVisible(false);
        patientInfoContainer.setManaged(false);
        

        util.AlertUtil.showError(null, "Erreur", message);
    }
} 