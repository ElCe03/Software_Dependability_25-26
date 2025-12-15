package entite;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

/**
 * Represents a medical record containing all of a patient's medical information
 */
public class DossierMedicale {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private User patient;        // corresponds to patient_id in SQL
    /*@ spec_public nullable @*/ private User medecin;        // corresponds to medecin_id in SQL
    /*@ spec_public nullable @*/ private LocalDateTime dateDeCreation;
    /*@ spec_public nullable @*/ private String historiqueDesMaladies;
    /*@ spec_public nullable @*/ private String operationsPassees;
    /*@ spec_public nullable @*/ private String consultationsPassees;
    /*@ spec_public nullable @*/ private String statutDossier;
    /*@ spec_public nullable @*/ private String notes;
    /*@ spec_public nullable @*/ private String image;
    /*@ spec_public non_null @*/private List<Sejour> sejours;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant sejours != null; @*/
    
    // Default constructor
    public DossierMedicale() {
        this.sejours = new ArrayList<Sejour>();
    }
    
    // Constructor with all fields
    public DossierMedicale(User patient, User medecin, LocalDateTime dateDeCreation, 
            String historiqueDesMaladies, String operationsPassees, String consultationsPassees, 
            String statutDossier, String notes, String image) {
        this.patient = patient;
        this.medecin = medecin;
        this.dateDeCreation = dateDeCreation;
        this.historiqueDesMaladies = historiqueDesMaladies;
        this.operationsPassees = operationsPassees;
        this.consultationsPassees = consultationsPassees;
        this.statutDossier = statutDossier;
        this.notes = notes;
        this.image = image;
        this.sejours = new ArrayList<Sejour>();
    }
    
    // Getters and Setters

    /*@ pure @*/
    public int getId() {
        return id;
    }
    
    public void setId(int id) {
        this.id = id;
    }
    
    // *** ECCO LA PARTE CRUCIALE CHE PREVIENE IL CRASH ***
    /*@ pure @*/
    public User getPatient() {
        return patient;
    }
    
    public void setPatient(User patient) {
        this.patient = patient;
    }
    
    /*@ pure @*/
    public User getMedecin() {
        return medecin;
    }
    
    public void setMedecin(User medecin) {
        this.medecin = medecin;
    }
    
    /*@ pure @*/
    public LocalDateTime getDateDeCreation() {
        return dateDeCreation;
    }
    
    public void setDateDeCreation(LocalDateTime dateDeCreation) {
        this.dateDeCreation = dateDeCreation;
    }
    
    /*@ pure @*/
    public String getHistoriqueDesMaladies() {
        return historiqueDesMaladies;
    }
    
    public void setHistoriqueDesMaladies(String historiqueDesMaladies) {
        this.historiqueDesMaladies = historiqueDesMaladies;
    }
    
    /*@ pure @*/
    public String getOperationsPassees() {
        return operationsPassees;
    }
    
    public void setOperationsPassees(String operationsPassees) {
        this.operationsPassees = operationsPassees;
    }
    
    /*@ pure @*/
    public String getConsultationsPassees() {
        return consultationsPassees;
    }
    
    public void setConsultationsPassees(String consultationsPassees) {
        this.consultationsPassees = consultationsPassees;
    }
    
    /*@ pure @*/
    public String getStatutDossier() {
        return statutDossier;
    }
    
    public void setStatutDossier(String statutDossier) {
        this.statutDossier = statutDossier;
    }
    
    /*@ pure @*/
    public String getNotes() {
        return notes;
    }
    
    public void setNotes(String notes) {
        this.notes = notes;
    }
    
    /*@ pure @*/
    public String getImage() {
        return image;
    }
    
    public void setImage(String image) {
        this.image = image;
    }
    
    /*@ pure @*/
    public List<Sejour> getSejours() {
        return sejours;
    }
    
    public void setSejours(List<Sejour> sejours) {
        this.sejours = sejours;
    }
    
    public void addSejour(Sejour sejour) {
        if(sejours == null) {
            sejours = new ArrayList<Sejour>();
        }
        sejours.add(sejour);
        if (sejour.getDossierMedicale() != this) {
            sejour.setDossierMedicale(this);
        }
    }
    
    /*@ pure @*/
    public int getPatientId() {
        return patient != null ? patient.getId() : 0;
    }
    
    /*@ pure @*/
    public int getMedecinId() {
        return medecin != null ? medecin.getId() : 0;
    }
    
    @Override
    public String toString() {
        return "Dossier #" + id;
    }
}
