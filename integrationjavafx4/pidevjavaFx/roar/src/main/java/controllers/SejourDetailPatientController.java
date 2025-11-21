package controllers;

import entite.DossierMedicale;
import entite.Sejour;
import entite.User;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.stage.Stage;
import service.DossierMedicaleService;
import service.UserService;
import service.UserServiceE;

import java.net.URL;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.ResourceBundle;
import java.util.logging.Level;
import java.util.logging.Logger;

public class SejourDetailPatientController implements Initializable {
    
    @FXML
    private Label lblId;
    
    @FXML
    private Label lblDateEntree;
    
    @FXML
    private Label lblDateSortie;
    
    @FXML
    private Label lblTypeSejour;
    
    @FXML
    private Label lblFraisSejour;
    
    @FXML
    private Label lblPrixExtras;
    
    @FXML
    private Label lblMoyenPaiement;
    
    @FXML
    private Label lblStatutPaiement;
    
    @FXML
    private Label lblStatutIndicator;
    
    @FXML
    private Label lblTotal;
    
    @FXML
    private Label lblDuree;
    
    @FXML
    private Label lblPatientNom;
    
    private Sejour sejour;
    private UserServiceE userServiceE;
    private DossierMedicaleService dossierService;
    
    private static final DateTimeFormatter DATE_FORMATTER = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");
    private static final Logger logger = Logger.getLogger(SejourDetailPatientController.class.getName());
    
    /*@ public normal_behavior
    @   assignable userServiceE, dossierService;
    @   ensures userServiceE != null;
    @   ensures dossierService != null;
    @*/

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        userServiceE = new UserServiceE();
        dossierService = new DossierMedicaleService();
    }
    
    /*@ public normal_behavior
    @   requires lblId != null && lblDateEntree != null && lblDateSortie != null &&
    @            lblTypeSejour != null && lblFraisSejour != null && lblPrixExtras != null &&
    @            lblMoyenPaiement != null && lblStatutPaiement != null &&
    @            lblStatutIndicator != null && lblTotal != null &&
    @            lblDuree != null && lblPatientNom != null;
    @
    @   assignable this.sejour,
    @              lblId.text, lblDateEntree.text, lblDateSortie.text,
    @              lblTypeSejour.text, lblFraisSejour.text, lblPrixExtras.text,
    @              lblMoyenPaiement.text, lblStatutPaiement.text,
    @              lblStatutIndicator.text, lblStatutIndicator.style,
    @              lblTotal.text, lblDuree.text, lblPatientNom.text;
    @
    @   ensures this.sejour == sejour;
    @*/

    /**
     * Set the sejour and display its details
     * @param sejour The sejour to display
     */
    public void setSejour(Sejour sejour) {
        this.sejour = sejour;
        displaySejourDetails();
    }

    /*@ private normal_behavior
    @   requires sejour != null;
    @   requires lblId != null && lblDateEntree != null && lblDateSortie != null &&
    @            lblTypeSejour != null && lblFraisSejour != null && lblPrixExtras != null &&
    @            lblMoyenPaiement != null && lblStatutPaiement != null &&
    @            lblStatutIndicator != null && lblTotal != null &&
    @            lblDuree != null && lblPatientNom != null;
    @
    @   assignable lblId.text, lblDateEntree.text, lblDateSortie.text,
    @              lblTypeSejour.text, lblFraisSejour.text, lblPrixExtras.text,
    @              lblMoyenPaiement.text, lblStatutPaiement.text,
    @              lblStatutIndicator.text, lblStatutIndicator.style,
    @              lblTotal.text, lblDuree.text, lblPatientNom.text;
    @
    @   ensures lblId.getText().equals(String.valueOf(sejour.getId()));
    @
    @ also private normal_behavior
    @   requires sejour == null;
    @   assignable \nothing;
    @   ensures true;
    @*/
    
    /**
     * Display the details of the current sejour
     */
    private void displaySejourDetails() {
        if (sejour == null) {
            logger.severe("Error: sejour is null in displaySejourDetails");
            return;
        }
        
        // Basic Info
        lblId.setText(String.valueOf(sejour.getId()));
        
        LocalDateTime dateEntree = sejour.getDateEntree();
        lblDateEntree.setText(dateEntree != null ? dateEntree.format(DATE_FORMATTER) : "Non définie");
        
        LocalDateTime dateSortie = sejour.getDateSortie();
        lblDateSortie.setText(dateSortie != null ? dateSortie.format(DATE_FORMATTER) : "Non définie");
        
        lblTypeSejour.setText(sejour.getTypeSejour() != null ? sejour.getTypeSejour() : "Non défini");
        
        // Calculate and display stay duration if both dates are available
        if (dateEntree != null && dateSortie != null) {
            long days = ChronoUnit.DAYS.between(dateEntree.toLocalDate(), dateSortie.toLocalDate());
            if (lblDuree != null) {
                lblDuree.setText(days + " jour" + (days > 1 ? "s" : ""));
            }
        } else if (lblDuree != null) {
            lblDuree.setText("Non calculable");
        }
        
        // Get patient information
        loadPatientInfo();
        
        // Payment Info
        Double fraisSejour = sejour.getFraisSejour();
        lblFraisSejour.setText(fraisSejour != null ? String.format("%.2f €", fraisSejour) : "0.00 €");
        
        Double prixExtras = sejour.getPrixExtras();
        lblPrixExtras.setText(prixExtras != null ? String.format("%.2f €", prixExtras) : "0.00 €");
        
        lblMoyenPaiement.setText(sejour.getMoyenPaiement() != null ? sejour.getMoyenPaiement() : "Non défini");
        
        // Status with colored indicator
        String statut = sejour.getStatutPaiement();
        lblStatutPaiement.setText(statut != null ? statut : "Non défini");
        
        // Set the right style and color for the status indicator
        setStatusIndicator(statut);
        
        // Calculate and display total
        double total = (fraisSejour != null ? fraisSejour : 0) + (prixExtras != null ? prixExtras : 0);
        lblTotal.setText(String.format("%.2f €", total));
    }

    /*@ private normal_behavior
        @   requires sejour != null;
    @   requires dossierService != null && userServiceE != null;
    @   requires lblPatientNom != null;
    @
    @   assignable lblPatientNom.text;
    @
    @   ensures lblPatientNom.getText() != null;
    @*/

    
    /**
     * Loads patient information based on the Sejour's DossierMedicale
     */
    private void loadPatientInfo() {
        if (lblPatientNom == null) {
            return;
        }
        
        try {
            // First, check if Sejour has a DossierMedicale with a patient
            if (sejour.getDossierMedicale() != null && sejour.getDossierMedicale().getPatient() != null) {
                User patient = sejour.getDossierMedicale().getPatient();
                lblPatientNom.setText(patient.getPrenom() + " " + patient.getNom());
                return;
            }
            
            // If DossierMedicale is not fully loaded, try to get it by ID
            if (sejour.getDossierMedicale() != null && sejour.getDossierMedicale().getId() > 0) {
                int dossierId = sejour.getDossierMedicale().getId();
                
                // Load the full DossierMedicale
                DossierMedicale dossier = dossierService.recupererDossierParId(dossierId, false);
                if (dossier != null && dossier.getPatient() != null) {
                    User patient = dossier.getPatient();
                    lblPatientNom.setText(patient.getPrenom() + " " + patient.getNom());
                    return;
                }
                
                // If DossierMedicale loaded but patient is not loaded, try to get patient by ID
                if (dossier != null && dossier.getPatientId() > 0) {
                    User patient = userServiceE.recupererUserParId(dossier.getPatientId());
                    if (patient != null) {
                        lblPatientNom.setText(patient.getPrenom() + " " + patient.getNom());
                        return;
                    }
                }
            }
            
            // If all else fails
            lblPatientNom.setText("Information patient non disponible");
            
        } catch (Exception e) {
            logger.log(Level.WARNING, "Error loading patient info", e);
            lblPatientNom.setText("Erreur de chargement");
        }
    }
    
    /*@ private normal_behavior
    @   requires lblStatutIndicator != null;
    @
    @   assignable lblStatutIndicator.text, lblStatutIndicator.style;
    @
    @   ensures lblStatutIndicator.getText() != null;
    @   ensures lblStatutIndicator.getStyle() != null;
    @*/

    /**
     * Sets the status indicator style based on payment status
     * @param statut the payment status
     */
    private void setStatusIndicator(String statut) {
        if (lblStatutIndicator == null) {
            return;
        }
        
        if (statut != null) {
            lblStatutIndicator.setText(statut);
            
            switch (statut.toLowerCase()) {
                case "payé":
                    lblStatutIndicator.setStyle("-fx-background-color: #27ae60; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
                case "en attente":
                    lblStatutIndicator.setStyle("-fx-background-color: #f39c12; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
                case "partiel":
                    lblStatutIndicator.setStyle("-fx-background-color: #3498db; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
                case "annulé":
                    lblStatutIndicator.setStyle("-fx-background-color: #e74c3c; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
                case "remboursé":
                    lblStatutIndicator.setStyle("-fx-background-color: #9b59b6; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
                default:
                    lblStatutIndicator.setStyle("-fx-background-color: #95a5a6; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
                    break;
            }
        } else {
            lblStatutIndicator.setText("Non défini");
            lblStatutIndicator.setStyle("-fx-background-color: #95a5a6; -fx-text-fill: white; -fx-background-radius: 10; -fx-padding: 3 10;");
        }
    }

    /*@ public normal_behavior
    @   requires event != null;
    @   requires event.getSource() instanceof Node;
    @   assignable \everything;
    @ also
    @ public exceptional_behavior
    @   requires event == null || !(event.getSource() instanceof Node);
    @   assignable \nothing;
    @   signals (NullPointerException) event == null;
    @   signals (ClassCastException) event != null && !(event.getSource() instanceof Node);
    @*/
    
    /**
     * Close the window
     * @param event The action event
     */
    @FXML
    private void handleClose(ActionEvent event) {
        ((Stage) ((Node) event.getSource()).getScene().getWindow()).close();
    }
} 