package entite;

public class MedicamentCommande {

    /*@ spec_public non_null @*/
    private Commande commande;

    /*@ spec_public non_null @*/
    private Medicament medicament;
    
    /*@ spec_public @*/
    private int quantite;

    /*@ public invariant commande != null; @*/
    /*@ public invariant medicament != null; @*/
    /*@ public invariant quantite > 0; @*/

    /*@ 
      @ requires commande != null;
      @ requires medicament != null;
      @ requires quantite > 0;
      @ 
      @ ensures this.commande == commande;
      @ ensures this.medicament == medicament;
      @ ensures this.quantite == quantite;
      @*/
    public MedicamentCommande(Commande commande, Medicament medicament, int quantite) {
        this.commande = commande;
        this.medicament = medicament;
        this.quantite = quantite;

    }

    // Getters/Setters

    /*@ ensures \result == commande; ensures \result != null; pure @*/
    public Commande getCommande() { return commande; }
    /*@ ensures \result == medicament; ensures \result != null; pure @*/
    public Medicament getMedicament() { return medicament; }
    /*@ ensures \result == quantite; ensures \result > 0; pure @*/
    public int getQuantite() { return quantite; }
    /*@ 
      @ requires commande != null;
      @ assignable this.commande;
      @ ensures this.commande == commande;
      @*/
    public void setCommande(Commande commande) {
        this.commande = commande;
    }
}
