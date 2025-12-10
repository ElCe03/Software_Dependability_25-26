package entite;

import java.sql.Timestamp;

public class reservation {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private salle salle;
    /*@ spec_public nullable @*/ private Timestamp date_debut;
    /*@ spec_public nullable @*/ private Timestamp date_fin;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant (date_debut != null && date_fin != null) ==> date_debut.before(date_fin); @*/

    /*@ 
      @ requires date_debut != null;
      @ requires date_fin != null;
      @ requires date_debut.before(date_fin);
      @ 
      @ requires id >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.salle == salle;
      @ ensures this.date_debut == date_debut;
      @ ensures this.date_fin == date_fin;
      @*/
    // Constructors
    public reservation(int id, salle salle, Timestamp date_debut, Timestamp date_fin) {
        this.id = id;
        this.salle = salle;
        this.date_debut = date_debut;
        this.date_fin = date_fin;
    }

    /*@ 
      @ ensures id == 0;
      @ ensures date_debut == null;
      @ ensures date_fin == null;
      @ ensures salle == null;
      @*/
    public reservation() {}


    // Getters and setters

    /*@ ensures \result == id; pure @*/
    public int getId() { return id; }
    
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) { this.id = id; }

    /*@ ensures \result == salle; pure @*/
    public salle getSalle() { return salle; }

    /*@ assignable this.salle; ensures this.salle == salle; @*/
    public void setSalle(salle salle) { this.salle = salle; }

    /*@ ensures \result == date_debut; pure @*/
    public Timestamp getDate_debut() { return date_debut; }

    /*@
      @ requires (this.date_fin != null && date_debut != null) ==> date_debut.before(this.date_fin);
      @ assignable this.date_debut;
      @ ensures this.date_debut == date_debut;
      @*/
    public void setDate_debut(Timestamp date_debut) { this.date_debut = date_debut; }

    /*@ ensures \result == date_fin; pure @*/
    public Timestamp getDate_fin() { return date_fin; }

    /*@ 
      @ requires (this.date_debut != null && date_fin != null) ==> this.date_debut.before(date_fin);
      @ assignable this.date_fin;
      @ ensures this.date_fin == date_fin;
      @*/
    public void setDate_fin(Timestamp date_fin) { this.date_fin = date_fin; }
}