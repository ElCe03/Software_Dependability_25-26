package entite;

import java.sql.Date;
import java.time.LocalDate;

public class Medicament {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String nom_medicament;
    /*@ spec_public nullable @*/ private String description_medicament;
    /*@ spec_public nullable @*/ private String type_medicament;
    /*@ spec_public @*/ private double prix_medicament;
    /*@ spec_public @*/ private int quantite_stock;
    /*@ spec_public nullable @*/ private LocalDate date_entree;
    /*@ spec_public nullable @*/ private LocalDate date_expiration;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant prix_medicament >= 0.0; @*/
    /*@ public invariant quantite_stock >= 0; @*/
    /*@ public invariant (date_entree != null && date_expiration != null) ==> 
      @     !date_expiration.isBefore(date_entree); 
      @*/

    /*@ 
      @ ensures id == 0;
      @ ensures prix_medicament == 0.0;
      @ ensures quantite_stock == 0;
      @*/
    public Medicament() {

    }

    /*@ 
      @ requires id >= 0;
      @ requires prix_medicament >= 0.0;
      @ requires quantite_stock >= 0;
      @ requires (date_entree != null && date_expiration != null) ==> !date_expiration.isBefore(date_entree);
      @ 
      @ ensures this.id == id;
      @ ensures this.prix_medicament == prix_medicament;
      @ ensures this.quantite_stock == quantite_stock;
      @ ensures this.date_entree == date_entree;
      @ ensures this.date_expiration == date_expiration;
      @*/
    public Medicament(int id, String nom_medicament, String description_medicament, String type_medicament, double prix_medicament, int quantite_stock,
                      LocalDate date_entree, LocalDate date_expiration) {
        this.id = id;
        this.nom_medicament = nom_medicament;
        this.description_medicament = description_medicament;
        this.type_medicament = type_medicament;
        this.prix_medicament = prix_medicament;
        this.quantite_stock = quantite_stock;
        this.date_entree = date_entree;
        this.date_expiration = date_expiration;
    }


    /*@ 
      @ requires prix_medicament >= 0.0;
      @ requires quantite_Stock >= 0;
      @ requires (date_entree != null && date_expiration != null) ==> !date_expiration.isBefore(date_entree);
      @ 
      @ ensures this.prix_medicament == prix_medicament;
      @ ensures this.quantite_stock == quantite_Stock;
      @*/
    // Constructeur sans l'id (l'id sera géré par la base de données)
    public Medicament(String nom_medicament, String description_medicament,
                      String type_medicament, double prix_medicament,
                      int quantite_Stock, LocalDate date_entree, LocalDate date_expiration) {
        this.nom_medicament = nom_medicament;
        this.description_medicament = description_medicament;
        this.type_medicament = type_medicament;
        this.prix_medicament = prix_medicament;
        this.quantite_stock = quantite_Stock;
        this.date_entree = date_entree;
        this.date_expiration = date_expiration;
    }

    // Getters et Setters

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }

    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    public String getNom_medicament() {
        return nom_medicament;
    }

    public void setNom_medicament(String nom_medicament) {
        this.nom_medicament = nom_medicament;
    }

    public String getDescription_medicament() {
        return description_medicament;
    }

    public void setDescription_medicament(String description_medicament) {
        this.description_medicament = description_medicament;
    }

    public String getType_medicament() {
        return type_medicament;
    }

    public void setType_medicament(String type_medicament) {
        this.type_medicament = type_medicament;
    }

    /*@ ensures \result == prix_medicament; pure @*/
    public double getPrix_medicament() {
        return prix_medicament;
    }

    /*@ 
      @ requires prix_medicament >= 0.0;
      @ assignable this.prix_medicament;
      @ ensures this.prix_medicament == prix_medicament;
      @*/
    public void setPrix_medicament(double prix_medicament) {
        this.prix_medicament = prix_medicament;
    }

    /*@ ensures \result == quantite_stock; pure @*/
    public int getQuantite_stock() {
        return quantite_stock;
    }

    /*@ 
      @ requires quantite_Stock >= 0;
      @ assignable this.quantite_stock;
      @ ensures this.quantite_stock == quantite_Stock;
      @*/
    public void setQuantite_stock(int quantite_Stock) {
        this.quantite_stock = quantite_Stock;
    }

    public LocalDate getDate_entree() {
        return date_entree;
    }

    /*@ 
      @ requires (this.date_expiration != null && date_entree != null) ==> !date_entree.isAfter(this.date_expiration);
      @ assignable this.date_entree;
      @ ensures this.date_entree == date_entree;
      @*/
    public void setDate_entree(LocalDate date_entree) {
        this.date_entree = date_entree;
    }

    public LocalDate getDate_expiration() {
        return date_expiration;
    }

    /*@ 
      @ requires (this.date_entree != null && date_expiration != null) ==> !date_expiration.isBefore(this.date_entree);
      @ assignable this.date_expiration;
      @ ensures this.date_expiration == date_expiration;
      @*/
    public void setDate_expiration(LocalDate date_expiration) {
        this.date_expiration = date_expiration;
    }

    @Override
    public String toString() {
        return this.nom_medicament;
    }
}
