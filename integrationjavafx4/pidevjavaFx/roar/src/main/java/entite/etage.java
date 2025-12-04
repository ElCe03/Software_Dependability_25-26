package entite;

public class etage {

    /*@ spec_public @*/ private int id;
    /*@ spec_public @*/ private int numero;
    /*@ spec_public @*/ private int  nbrSalle = 0; // Initialisé à 0
    /*@ spec_public nullable @*/ private entite.departement departement;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant nbrSalle >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures numero == 0;
      @ ensures nbrSalle == 0;
      @ ensures departement == null;
      @*/
    public etage() {}

    /*@ 
      @ requires id >= 0;
      @ 
      @ ensures this.id == id;
      @ ensures this.numero == numero;
      @ ensures this.departement == departement;
      @ ensures this.nbrSalle == 0;
      @*/
    public etage(int id, int numero, entite.departement departement) {
        this.id = id;
        this.numero = numero;
        this.departement = departement;
    }

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }

    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ ensures \result == numero; pure @*/
    public int getNumero() {
        return numero;
    }

    /*@ assignable this.numero; ensures this.numero == numero; @*/
    public void setNumero(int numero) {
        this.numero = numero;
    }

    /*@ ensures \result == departement; pure @*/
    public entite.departement getDepartement() {
        return departement;
    }

    /*@ assignable this.departement; ensures this.departement == departement; @*/
    public void setDepartement(entite.departement departement) {
        this.departement = departement;
    }

    /*@ ensures \result == nbrSalle; pure @*/
    public int getNbrSalle() {
        return nbrSalle;
    }

    /*@ 
      @ requires nbrSalle >= 0;
      @ assignable this.nbrSalle;
      @ ensures this.nbrSalle == nbrSalle;
      @*/
    public void setNbrSalle(int nbrSalle) {
        this.nbrSalle = nbrSalle;
    }
}
