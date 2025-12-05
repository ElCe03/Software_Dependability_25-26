package entite;

public class MedicamentCommande {
    private Commande commande;
    private Medicament medicament;
    private int quantite;


    public MedicamentCommande(Commande commande, Medicament medicament, int quantite) {
        this.commande = commande;
        this.medicament = medicament;
        this.quantite = quantite;

    }

    // Getters/Setters
    public Commande getCommande() { return commande; }
    public Medicament getMedicament() { return medicament; }
    public int getQuantite() { return quantite; }

    public void setCommande(Commande commande) {
        this.commande = commande;
    }
}
