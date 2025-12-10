package entite;

public class Equipement {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String nom;
    /*@ spec_public nullable @*/ private String type;
    /*@ spec_public nullable @*/ private String statut;
    /*@ spec_public nullable @*/ private String category;

    /*@ public invariant id >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures nom == null;
      @ ensures type == null;
      @ ensures statut == null;
      @ ensures category == null;
      @*/
    // Constructeurs
    public Equipement() {}

    /*@ 
      @ requires id >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.nom == nom;
      @ ensures this.type == type;
      @ ensures this.statut == statut;
      @ ensures this.category == category;
      @*/
    public Equipement(int id, String nom, String type, String statut, String category) {
        this.id = id;
        this.nom = nom;
        this.type = type;
        this.statut = statut;
        this.category = category;
    }

    /*@ 
      @ ensures this.id == 0; // Default int value
      @ ensures this.nom == nom;
      @ ensures this.type == type;
      @ ensures this.statut == statut;
      @ ensures this.category == category;
      @*/
    public Equipement(String nom, String type, String statut, String category) {
        this.nom = nom;
        this.type = type;
        this.statut = statut;
        this.category = category;
    }

    // Getters et Setters

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }

    /*@ 
      @ requires id >= 0;
      @ assignable this.id;
      @ ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ pure @*/
    public String getNom() {
        return nom;
    }

    /*@ assignable this.nom; @*/
    public void setNom(String nom) {
        this.nom = nom;
    }

    /*@ pure @*/
    public String getType() {
        return type;
    }

    /*@ assignable this.type; @*/
    public void setType(String type) {
        this.type = type;
    }

    /*@ pure @*/
    public String getStatut() {
        return statut;
    }

    /*@ assignable this.statut; @*/
    public void setStatut(String statut) {
        this.statut = statut;
    }

    /*@ pure @*/
    public String getCategory() {
        return category;
    }

    /*@ assignable this.category; @*/
    public void setCategory(String category) {
        this.category = category;
    }

    // toString pour affichage (facultatif)
    @Override
    public String toString() {
        return "Equipement{" +
                "id=" + id +
                ", nom='" + nom + '\'' +
                ", type='" + type + '\'' +
                ", statut='" + statut + '\'' +
                ", category='" + category + '\'' +
                '}';
    }
}
