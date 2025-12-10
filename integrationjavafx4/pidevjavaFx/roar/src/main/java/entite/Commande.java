package entite;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class Commande {
    
    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private LocalDate date_commande;
    /*@ spec_public @*/ private double total_prix;
    /*@ spec_public @*/ private int quantite;
    /*@ spec_public non_null @*/ private List<MedicamentCommande> medicamentsCommandes;
    /*@ spec_public nullable @*/ private String stripeSessionId;
    /*@ spec_public nullable @*/ private String status;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant total_prix >= 0.0; @*/
    /*@ public invariant quantite >= 0; @*/
    /*@ public invariant medicamentsCommandes != null; @*/
    /*@ public invariant (\forall int i; 0 <= i && i < medicamentsCommandes.size(); medicamentsCommandes.get(i) != null); @*/

    /*@ 
      @ ensures id == 0;
      @ ensures total_prix == 0.0;
      @ ensures quantite == 0;
      @ ensures medicamentsCommandes != null && medicamentsCommandes.isEmpty();
      @*/
    public Commande() {
        this.medicamentsCommandes = new ArrayList<MedicamentCommande>();
    }

    /*@ 
      @ requires id >= 0;
      @ requires total_prix >= 0.0;
      @ requires quantite >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.total_prix == total_prix;
      @ ensures this.quantite == quantite;
      @ ensures this.medicamentsCommandes != null && this.medicamentsCommandes.isEmpty();
      @*/
    // Constructeur
    public Commande(int id, LocalDate date_commande, double total_prix, int quantite) {
        this.id = id;
        this.date_commande = date_commande;
        this.total_prix = total_prix;
        this.quantite = quantite;
        this.medicamentsCommandes = new ArrayList<MedicamentCommande>();
    }

    // Getters/Setters

    /*@ ensures \result == id; pure @*/
    public int getId() { return id; }
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) { this.id = id; }

    /*@ pure @*/
    public LocalDate getDate_commande() { return date_commande; }
    /*@ assignable this.date_commande; @*/
    public void setDate_commande(LocalDate date_commande) { this.date_commande = date_commande; }

    /*@ ensures \result == total_prix; pure @*/
    public double getTotal_prix() { return total_prix; }
    /*@ 
      @ requires total_prix >= 0.0;
      @ assignable this.total_prix;
      @ ensures this.total_prix == total_prix;
      @*/
    public void setTotal_prix(double total_prix) { this.total_prix = total_prix; }

    /*@ ensures \result == quantite; pure @*/
    public int getQuantite() { return quantite; } // New getter
    /*@ 
      @ requires quantite >= 0;
      @ assignable this.quantite;
      @ ensures this.quantite == quantite;
      @*/
    public void setQuantite(int quantite) { this.quantite = quantite; }

    /*@ ensures \result == medicamentsCommandes; ensures \result != null; pure @*/
    public List<MedicamentCommande> getMedicaments() { return medicamentsCommandes; }
    /*@ 
      @ requires m != null;
      @ requires quantite > 0;
      @ 
      @ ensures medicamentsCommandes.size() == \old(medicamentsCommandes.size()) + 1;
      @*/
    public void addMedicament(Medicament m, int quantite) {
        this.medicamentsCommandes.add(new MedicamentCommande(this, m, quantite));
    }

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public String getNomMedicamentsCommandes() {
        if (medicamentsCommandes == null || medicamentsCommandes.isEmpty()) return "";
        return medicamentsCommandes.stream()
                .map(mc -> mc.getMedicament().getNom_medicament())
                .collect(Collectors.joining(", "));
    }
    public String getStripeSessionId() { return stripeSessionId; }
    public void setStripeSessionId(String stripeSessionId) { this.stripeSessionId = stripeSessionId; }

    public String getStatus() { return status; }
    public void setStatus(String status) { this.status = status; }

}