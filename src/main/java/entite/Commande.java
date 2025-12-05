package entite;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class Commande {
    private int id;
    private LocalDate date_commande;
    private double total_prix;
    private int quantite;
    private List<MedicamentCommande> medicamentsCommandes;
    private String stripeSessionId;
    private String status;


    public Commande() {
        this.medicamentsCommandes = new ArrayList<>();
    }

    // Constructeur
    public Commande(int id, LocalDate date_commande, double total_prix, int quantite) {
        this.id = id;
        this.date_commande = date_commande;
        this.total_prix = total_prix;
        this.quantite = quantite;
        this.medicamentsCommandes = new ArrayList<>();
    }

    // Getters/Setters
    public int getId() { return id; }
    public void setId(int id) { this.id = id; }

    public LocalDate getDate_commande() { return date_commande; }
    public void setDate_commande(LocalDate date_commande) { this.date_commande = date_commande; }

    public double getTotal_prix() { return total_prix; }
    public void setTotal_prix(double total_prix) { this.total_prix = total_prix; }

    public int getQuantite() { return quantite; } // New getter
    public void setQuantite(int quantite) { this.quantite = quantite; }

    public List<MedicamentCommande> getMedicaments() { return medicamentsCommandes; }
    public void addMedicament(Medicament m, int quantite) {
        this.medicamentsCommandes.add(new MedicamentCommande(this, m, quantite));
    }

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