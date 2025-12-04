package entite;

import java.time.LocalDate;
import java.time.LocalDateTime;

public class Entretien {

    /*@ spec_public @*/ private int id;
    /*@ spec_public @*/ private int equipementId;
    /*@ spec_public nullable @*/ private LocalDate date;
    /*@ spec_public nullable @*/ private String description;
    /*@ spec_public nullable @*/ private String nomEquipement;
    /*@ spec_public nullable @*/ private LocalDateTime createdAt;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant equipementId >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures equipementId == 0;
      @ ensures date == null;
      @*/
    public Entretien() {}

    /*@ 
      @ requires id >= 0;
      @ requires equipementId >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.equipementId == equipementId;
      @ ensures this.date == date;
      @ ensures this.description == description;
      @ ensures this.nomEquipement == nomEquipement;
      @ ensures this.createdAt == createdAt;
      @*/
    public Entretien(int id, int equipementId, LocalDate date, String description, String nomEquipement, LocalDateTime createdAt) {
        this.id = id;
        this.equipementId = equipementId;
        this.date = date;
        this.description = description;
        this.nomEquipement = nomEquipement;
        this.createdAt = createdAt;
    }

    /*@ 
      @ requires equipementId >= 0;
      @ 
      @ ensures this.id == 0;
      @ ensures this.equipementId == equipementId;
      @ ensures this.date == date;
      @ ensures this.createdAt == createdAt;
      @*/
    public Entretien(int equipementId, LocalDate date, String description, String nomEquipement, LocalDateTime createdAt) {
        this.equipementId = equipementId;
        this.date = date;
        this.description = description;
        this.nomEquipement = nomEquipement;
        this.createdAt = createdAt;
    }

    // Getters

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }

    /*@ ensures \result == equipementId; pure @*/
    public int getEquipementId() {
        return equipementId;
    }

    /*@ pure @*/
    public LocalDate getDate() {
        return date;
    }

    /*@ pure @*/
    public String getDescription() {
        return description;
    }

    /*@ pure @*/
    public String getNomEquipement() {
        return nomEquipement;
    }

    /*@ pure @*/
    public LocalDateTime getCreatedAt() {
        return createdAt;
    }

    // Setters

    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ 
      @ requires equipementId >= 0; 
      @ assignable this.equipementId; 
      @ ensures this.equipementId == equipementId; 
      @*/
    public void setEquipementId(int equipementId) {
        this.equipementId = equipementId;
    }

    /*@ assignable this.date; @*/
    public void setDate(LocalDate date) {
        this.date = date;
    }

    /*@ assignable this.description; @*/
    public void setDescription(String description) {
        this.description = description;
    }

    /*@ assignable this.nomEquipement; @*/
    public void setNomEquipement(String nomEquipement) {
        this.nomEquipement = nomEquipement;
    }

    /*@ assignable this.createdAt; @*/
    public void setCreatedAt(LocalDateTime createdAt) {
        this.createdAt = createdAt;
    }

    // Affichage
    @Override
    public String toString() {
        return "Entretien{" +
                "id=" + id +
                ", equipementId=" + equipementId +
                ", date=" + date +
                ", description='" + description + '\'' +
                ", nomEquipement='" + nomEquipement + '\'' +
                ", createdAt=" + createdAt +
                '}';
    }
}
