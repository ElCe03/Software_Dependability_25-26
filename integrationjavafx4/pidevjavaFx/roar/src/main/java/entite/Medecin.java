package entite;
import jakarta.persistence.DiscriminatorValue;
import jakarta.persistence.Entity;

import java.util.ArrayList;
import java.util.List;
@Entity
@DiscriminatorValue("MEDECIN")

public class Medecin extends Users{

    /*@ spec_public nullable @*/ private String specialite;
    /*@ spec_public nullable @*/ private String telephone;

    /*@ 
      @ ensures roles != null && roles.isEmpty();
      @ ensures specialite == null;
      @ ensures telephone == null;
      @*/
    public Medecin() {
        super();
    }

    /*@ 
      @ requires roles != null ==> (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null);
      @ 
      @ ensures this.id == id;
      @ ensures this.email == email;
      @ ensures this.specialite == specialite;
      @ ensures this.telephone == telephone;
      @ 
      @ ensures (roles != null) ==> this.roles == roles;
      @ ensures (roles == null) ==> (this.roles != null && this.roles.isEmpty());
      @*/
    public Medecin(int id, String email, String password, List<String> roles, String nom, String prenom,String type,
                   String specialite, String telephone) {
        super(id, email, password, roles, nom, prenom,type);
        this.specialite = specialite;
        this.telephone = telephone;
    }

    /*@ pure @*/
    public String getSpecialite() {
        return specialite;
    }

    /*@ assignable this.specialite; @*/
    public void setSpecialite(String specialite) {
        this.specialite = specialite;
    }

    /*@ pure @*/
    public String getTelephone() {
        return telephone;
    }

    /*@ assignable this.telephone; @*/
    public void setTelephone(String telephone) {
        this.telephone = telephone;
    }


    @Override
    public String toString() {
        return "Medecin{" +
                "id=" + getId() +
                ", email='" + getEmail() + '\'' +
                ", nom='" + getNom() + '\'' +
                ", prenom='" + getPrenom() + '\'' +
                ", roles=" + getRoles() +
                ", specialite='" + specialite + '\'' +
                ", telephone='" + telephone + '\'' +
                '}';
    }

}
