package entite;

public class salle {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String nom;
    /*@ spec_public @*/ private int capacite;
    /*@ spec_public nullable @*/ private String type_salle;
    /*@ spec_public nullable @*/ private String status;
    /*@ spec_public nullable @*/ private etage etage;
    /*@ spec_public nullable @*/ private String image;
    /*@ spec_public @*/ private int priorite;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant capacite >= 0; @*/
    /*@ public invariant priorite >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures capacite == 0;
      @ ensures priorite == 0;
      @*/
    public salle() {}

    /*@ 
      @ requires capacite >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.nom == nom;
      @ ensures this.capacite == capacite;
      @ ensures this.status == status;
      @*/
    public salle(int id, String nom, int capacite,  String status) {
        this.id = id;
        this.nom = nom;
        this.capacite = capacite;
        this.status = status;

    }

    /*@ 
      @ ensures this.id == id;
      @ ensures this.nom == nom;
      @ ensures this.status == status;
      @ ensures this.capacite == 0;
      @*/
    public salle(int id,String nom,String status) {
        this.id = id;
        this.nom = nom;
        this.status = status;
    }

    /*@ 
      @ requires capacite >= 0;
      @ requires priorite >= 0;
      @ 
      @ ensures this.nom == nom;
      @ ensures this.capacite == capacite;
      @ ensures this.type_salle == type_salle;
      @ ensures this.image == image;
      @ ensures this.status == status;
      @ ensures this.priorite == priorite;
      @*/
    public salle( String nom, int capacite, String type_salle, String image,String status  ,int priorite) {
        this.nom = nom;
        this.capacite = capacite;
        this.type_salle = type_salle;
        this.image = image;
        this.status = status;
        this.priorite = priorite;

    }

    // Getters et setters

    /*@ ensures \result == id; pure @*/
    public int getId() { return id; }
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) { this.id = id; }

    /*@ pure @*/
    public String getNom() { return nom; }
    /*@ assignable this.nom; @*/
    public void setNom(String nom) { this.nom = nom; }

    /*@ ensures \result == capacite; pure @*/
    public int getCapacite() { return capacite; }
    /*@ 
      @ requires capacite >= 0; 
      @ assignable this.capacite; 
      @ ensures this.capacite == capacite; 
      @*/
    public void setCapacite(int capacite) { this.capacite = capacite; }

    public String getType_salle() { return type_salle; }
    public void setType_salle(String type_salle) { this.type_salle = type_salle; }

    public String getStatus() { return status; }
    public void setStatus(String status) { this.status = status; }

    public etage getEtage() { return etage; }
    public void setEtage(etage etage) { this.etage = etage; }

    public String getImage() { return image; }
    public void setImage(String image) { this.image = image; }

    /*@ ensures \result == priorite; pure @*/
    public int getPriorite() { return priorite; }
    /*@ 
      @ requires priorite >= 0; 
      @ assignable this.priorite; 
      @ ensures this.priorite == priorite; 
      @*/
    public void setPriorite(int priorite) { this.priorite = priorite; }
}