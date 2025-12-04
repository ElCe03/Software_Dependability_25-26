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
    /*@ public invariant (\forall int i; 0 <= i && i < sejours.size(); sejours.get(i) != null); @*/
    
    /*@ 
      @ ensures id == 0;
      @ ensures sejours != null && sejours.isEmpty();
      @*/
    // Default constructor
    public DossierMedicale() {
        this.sejours = new ArrayList<>();
    }
    
    /*@ 
      @ ensures this.patient == patient;
      @ ensures this.medecin == medecin;
      @ ensures this.dateDeCreation == dateDeCreation;
      @ ensures this.sejours != null && this.sejours.isEmpty();
      @*/
    // Constructor with all fields except ID and sejours
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
        this.sejours = new ArrayList<>();
    }
    
    // Getters and Setters

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }
    
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }
    
    /*@ ensures \result == patient; pure @*/
    public User getPatient() {
        return patient;
    }
    
    /*@ assignable this.patient; ensures this.patient == patient; @*/
    public void setPatient(User patient) {
        this.patient = patient;
    }
    
    /*@ ensures \result == medecin; pure @*/
    public User getMedecin() {
        return medecin;
    }
    
    /*@ assignable this.medecin; ensures this.medecin == medecin; @*/
    public void setMedecin(User medecin) {
        this.medecin = medecin;
    }
    
    public LocalDateTime getDateDeCreation() {
        return dateDeCreation;
    }
    
    public void setDateDeCreation(LocalDateTime dateDeCreation) {
        this.dateDeCreation = dateDeCreation;
    }
    
    public String getHistoriqueDesMaladies() {
        return historiqueDesMaladies;
    }
    
    public void setHistoriqueDesMaladies(String historiqueDesMaladies) {
        this.historiqueDesMaladies = historiqueDesMaladies;
    }
    
    public String getOperationsPassees() {
        return operationsPassees;
    }
    
    public void setOperationsPassees(String operationsPassees) {
        this.operationsPassees = operationsPassees;
    }
    
    public String getConsultationsPassees() {
        return consultationsPassees;
    }
    
    public void setConsultationsPassees(String consultationsPassees) {
        this.consultationsPassees = consultationsPassees;
    }
    
    public String getStatutDossier() {
        return statutDossier;
    }
    
    public void setStatutDossier(String statutDossier) {
        this.statutDossier = statutDossier;
    }
    
    public String getNotes() {
        return notes;
    }
    
    public void setNotes(String notes) {
        this.notes = notes;
    }
    
    public String getImage() {
        return image;
    }
    
    public void setImage(String image) {
        this.image = image;
    }
    
    /*@ ensures \result == sejours; ensures \result != null; pure @*/
    public List<Sejour> getSejours() {
        return sejours;
    }
    
    /*@ 
      @ requires sejours != null;
      @ assignable this.sejours;
      @ ensures this.sejours == sejours;
      @*/
    public void setSejours(List<Sejour> sejours) {
        this.sejours = sejours;
    }
    
    /*@ 
      @ requires sejour != null;
      @ 
      @ ensures sejours != null;
      @ ensures sejours.contains(sejour);
      @ ensures sejours.size() == \old(sejours.size()) + 1;
      @ 
      @ ensures sejour.getDossierMedicale() == this;
      @*/
    public void addSejour(Sejour sejour) {
        if(sejours == null) {
            sejours = new ArrayList<>();
        }
        sejours.add(sejour);
        
        // Ensure bi-directional relationship
        if (sejour.getDossierMedicale() != this) {
            sejour.setDossierMedicale(this);
        }
    }
    
    /*@ pure @*/
    // Helper method to get patient_id for database operations
    public int getPatientId() {
        return patient != null ? patient.getId() : 0;
    }
    
    /*@ pure @*/
    // Helper method to get medecin_id for database operations
    public int getMedecinId() {
        return medecin != null ? medecin.getId() : 0;
    }
    
    @Override
    public String toString() {
        return "Dossier #" + id + " - " + 
               (patient != null ? patient.getPrenom() + " " + patient.getNom() : "Patient non attribué");
    }
} 