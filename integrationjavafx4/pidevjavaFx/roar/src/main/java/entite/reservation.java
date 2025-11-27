package entite;

import java.sql.Timestamp;

public class reservation {
    private int id;
    private salle salle;
    private Timestamp date_debut;
    private Timestamp date_fin;

    // Constructors
    public reservation(int id, salle salle, Timestamp date_debut, Timestamp date_fin) {
        this.id = id;
        this.salle = salle;
        this.date_debut = date_debut;
        this.date_fin = date_fin;
    }
    public reservation() {}


    // Getters and setters
    public int getId() { return id; }
    public void setId(int id) { this.id = id; }
    public salle getSalle() { return salle; }
    public void setSalle(salle salle) { this.salle = salle; }
    public Timestamp getDate_debut() { return date_debut; }
    public void setDate_debut(Timestamp date_debut) { this.date_debut = date_debut; }
    public Timestamp getDate_fin() { return date_fin; }
    public void setDate_fin(Timestamp date_fin) { this.date_fin = date_fin; }
}