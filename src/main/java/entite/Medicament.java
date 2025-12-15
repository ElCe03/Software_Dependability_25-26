package entite;

import java.sql.Date;
import java.time.LocalDate;

public class Medicament {

    private int id;
    private String nom_medicament;
    private String description_medicament;
    private String type_medicament;
    private double prix_medicament;
    private int quantite_stock;
    private LocalDate date_entree;
    private LocalDate date_expiration;


    public Medicament() {

    }
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

    public int getId() {
        return id;
    }

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

    public double getPrix_medicament() {
        return prix_medicament;
    }

    public void setPrix_medicament(double prix_medicament) {
        this.prix_medicament = prix_medicament;
    }

    public int getQuantite_stock() {
        return quantite_stock;
    }

    public void setQuantite_stock(int quantite_Stock) {
        this.quantite_stock = quantite_Stock;
    }

    public LocalDate getDate_entree() {
        return date_entree;
    }

    public void setDate_entree(LocalDate date_entree) {
        this.date_entree = date_entree;
    }

    public LocalDate getDate_expiration() {
        return date_expiration;
    }

    public void setDate_expiration(LocalDate date_expiration) {
        this.date_expiration = date_expiration;
    }

    @Override
    public String toString() {
        return this.nom_medicament;
    }
}
