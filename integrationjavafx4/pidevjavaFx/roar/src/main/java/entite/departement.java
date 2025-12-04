package entite;

public class departement {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String nom;
    /*@ spec_public nullable @*/ private String adresse;
    /*@ spec_public nullable @*/ private String image;
    /*@ spec_public @*/ private int nbr_etage;  // Attribut pour l'affichage seulement, non lié à la base de données

    /*@ public invariant id >= 0; @*/
    /*@ public invariant nbr_etage >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures nbr_etage == 0;
      @*/
    // Constructeurs
    public departement() {
        this.nbr_etage = 0;  // Initialisé à 0 par défaut
    }

    /*@ 
      @ ensures this.id == 0;
      @ ensures this.nom == nom;
      @ ensures this.adresse == adresse;
      @ ensures this.image == image;
      @ ensures this.nbr_etage == 0;
      @*/
    public departement(String nom, String adresse, String image) {
        this.nom = nom;
        this.adresse = adresse;
        this.image = image;
        this.nbr_etage = 0;  // Initialisé à 0 par défaut
    }

    /*@ 
      @ requires id >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.nom == nom;
      @ ensures this.adresse == adresse;
      @ ensures this.image == image;
      @ ensures this.nbr_etage == 0;
      @*/
    public departement(int id, String nom, String adresse, String image) {
        this.id = id;
        this.nom = nom;
        this.adresse = adresse;
        this.image = image;
        this.nbr_etage = 0;  // Initialisé à 0 par défaut
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
    /*@ pure @*/
    public String getAdresse() { return adresse; }
    /*@ assignable this.adresse; @*/
    public void setAdresse(String adresse) { this.adresse = adresse; }
    /*@ pure @*/
    public String getImage() { return image; }
    /*@ assignable this.image; @*/
    public void setImage(String image) { this.image = image; }

    // Getter et setter pour nbretage

    /*@ ensures \result == nbr_etage; pure @*/
    public int getNbr_etage() { return nbr_etage; }
    /*@ 
      @ // Protezione dell'invariante: Rifiutiamo valori negativi
      @ requires nbretage >= 0;
      @ assignable this.nbr_etage;
      @ ensures this.nbr_etage == nbretage;
      @*/
    public void setNbr_etage(int nbretage) { this.nbr_etage = nbretage; }

    // Méthode pour augmenter le nombre d'étages

    @Override
    public String toString() {
        return null;
    }

    public void setNbr_Etage(int i) {
    }

    // Méthode optionnelle pour diminuer le nombre d'étages

}