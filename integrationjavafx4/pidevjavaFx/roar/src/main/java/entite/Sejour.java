package entite;

import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;

/**
 * Represents a patient's stay at the medical facility
 * This class matches the sejour table in the database:
 * - id
 * - dossier_medicale_id (DossierMedicale reference)
 * - date_entree
 * - date_sortie
 * - type_sejour
 * - frais_sejour
 * - moyen_paiement
 * - statut_paiement
 * - prix_extras
 */
public class Sejour {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private LocalDateTime dateEntree;
    /*@ spec_public nullable @*/ private LocalDateTime dateSortie;
    /*@ spec_public nullable @*/ private String typeSejour;
    /*@ spec_public @*/ private double fraisSejour;
    /*@ spec_public nullable @*/ private String moyenPaiement;
    /*@ spec_public nullable @*/ private String statutPaiement;
    /*@ spec_public @*/ private double prixExtras;
    /*@ spec_public nullable @*/ private DossierMedicale dossierMedicale;  // corresponds to dossier_medicale_id in SQL
    
    // These fields don't exist in the database and should be marked as transient
    // so they aren't involved in database operations
    /*@ spec_public nullable @*/ private transient String chambre;  // Not in database
    /*@ spec_public nullable @*/ private transient String notes;    // Not in database
    
    /*@ public invariant id >= 0; @*/
    /*@ public invariant fraisSejour >= 0.0; @*/
    /*@ public invariant prixExtras >= 0.0; @*/

    /*@ 
      @ ensures fraisSejour == 0.0;
      @ ensures prixExtras == 0.0;
      @ ensures statutPaiement != null && statutPaiement.equals("En attente");
      @*/
    // Default constructor
    public Sejour() {
        // Initialize default values
        this.fraisSejour = 0.0;
        this.prixExtras = 0.0;
        this.statutPaiement = "En attente";
    }
    
    /*@ 
      @ requires fraisSejour >= 0.0;
      @ requires prixExtras >= 0.0;
      @ 
      @ ensures this.fraisSejour == fraisSejour;
      @ ensures this.prixExtras == prixExtras;
      @ ensures this.dateEntree == dateEntree;
      @ ensures this.dateSortie == dateSortie;
      @*/
    // Constructor with all fields that exist in the database
    public Sejour(LocalDateTime dateEntree, LocalDateTime dateSortie, String typeSejour, 
            double fraisSejour, String moyenPaiement, String statutPaiement, double prixExtras, 
            DossierMedicale dossierMedicale) {
        this.dateEntree = dateEntree;
        this.dateSortie = dateSortie;
        this.typeSejour = typeSejour;
        this.fraisSejour = fraisSejour;
        this.moyenPaiement = moyenPaiement;
        this.statutPaiement = statutPaiement;
        this.prixExtras = prixExtras;
        this.dossierMedicale = dossierMedicale;
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
    
    public LocalDateTime getDateEntree() {
        return dateEntree;
    }
    
    public void setDateEntree(LocalDateTime dateEntree) {
        this.dateEntree = dateEntree;
    }
    
    public LocalDateTime getDateSortie() {
        return dateSortie;
    }
    
    public void setDateSortie(LocalDateTime dateSortie) {
        this.dateSortie = dateSortie;
    }
    
    public String getTypeSejour() {
        return typeSejour;
    }
    
    public void setTypeSejour(String typeSejour) {
        this.typeSejour = typeSejour;
    }
    
    /*@ ensures \result == fraisSejour; pure @*/
    public double getFraisSejour() {
        return fraisSejour;
    }
    
    /*@ 
      @ requires fraisSejour >= 0.0;
      @ assignable this.fraisSejour;
      @ ensures this.fraisSejour == fraisSejour;
      @*/
    public void setFraisSejour(double fraisSejour) {
        this.fraisSejour = fraisSejour;
    }
    
    public String getMoyenPaiement() {
        return moyenPaiement;
    }
    
    public void setMoyenPaiement(String moyenPaiement) {
        this.moyenPaiement = moyenPaiement;
    }
    
    public String getStatutPaiement() {
        return statutPaiement;
    }
    
    public void setStatutPaiement(String statutPaiement) {
        this.statutPaiement = statutPaiement;
    }
    
    /*@ ensures \result == prixExtras; pure @*/
    public double getPrixExtras() {
        return prixExtras;
    }
    
    /*@ 
      @ requires prixExtras >= 0.0;
      @ assignable this.prixExtras;
      @ ensures this.prixExtras == prixExtras;
      @*/
    public void setPrixExtras(double prixExtras) {
        this.prixExtras = prixExtras;
    }
    
    /*@ ensures \result == dossierMedicale; 
      @ pure 
      @*/
    public DossierMedicale getDossierMedicale() {
        return dossierMedicale;
    }
    
    /*@ 
      @ ensures this.dossierMedicale == dossierMedicale;
      @*/
    public void setDossierMedicale(DossierMedicale dossierMedicale) {
        this.dossierMedicale = dossierMedicale;
        
        // Ensure bi-directional relationship
        if (dossierMedicale != null && !dossierMedicale.getSejours().contains(this)) {
            dossierMedicale.addSejour(this);
        }
    }
    
    // Transient getters and setters (not in database)
    public String getChambre() {
        return chambre;
    }
    
    public void setChambre(String chambre) {
        this.chambre = chambre;
    }
    
    public String getNotes() {
        return notes;
    }
    
    public void setNotes(String notes) {
        this.notes = notes;
    }
    
    // Helper method to get dossier_medicale_id for database operations
    /*@ pure @*/
    public int getDossierMedicaleId() {
        return dossierMedicale != null ? dossierMedicale.getId() : 0;
    }
    
    /**
     * Calculate the total cost of the stay including base cost and extras
     * @return The total cost
     */
    /*@ 
      @ ensures \result == fraisSejour + prixExtras;
      @ ensures \result >= 0.0;
      @ pure
      @*/
    public double calculateTotalCost() {
        return fraisSejour + prixExtras;
    }
    
    /**
     * Calculate the duration of the stay in days
     * @return The number of days of the stay
     */
    /*@ 
      @ ensures (dateEntree == null || dateSortie == null) ==> \result == 0;
      @ pure
      @*/
    public long calculateStayDuration() {
        if (dateEntree == null || dateSortie == null) {
            return 0;
        }
        
        LocalDate dateIn = dateEntree.toLocalDate();
        LocalDate dateOut = dateSortie.toLocalDate();
        return ChronoUnit.DAYS.between(dateIn, dateOut);
    }
    
    @Override
    public String toString() {
        return "Séjour #" + id + " - " + typeSejour + 
               " (" + (dateEntree != null ? dateEntree.toLocalDate() : "N/A") + 
               " à " + (dateSortie != null ? dateSortie.toLocalDate() : "N/A") + ")";
    }
} 