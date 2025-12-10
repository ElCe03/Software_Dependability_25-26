package entite;
import jakarta.persistence.DiscriminatorValue;
import jakarta.persistence.Entity;

import java.time.LocalDate;
import java.util.List;
@Entity
@DiscriminatorValue("PATIENT")

public class Patient extends Users {

    /*@ spec_public nullable @*/ private String adresse;
    /*@ spec_public nullable @*/ private String telephone;
    /*@ spec_public nullable @*/ private LocalDate dateNaissance;

    /*@ 
      @ ensures roles != null && roles.isEmpty();
      @ ensures adresse == null;
      @ ensures telephone == null;
      @ ensures dateNaissance == null;
      @*/
    public Patient() {
        super();
    }

    /*@ 
      @ requires roles != null ==> (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null);
      @ 
      @ ensures this.id == id;
      @ ensures this.email == email;
      @ ensures this.adresse == adresse;
      @ ensures this.telephone == telephone;
      @ ensures this.dateNaissance == dateNaissance;
      @ 
      @ ensures (roles != null) ==> this.roles == roles;
      @ ensures (roles == null) ==> (this.roles != null && this.roles.isEmpty());
      @*/
    public Patient(int id, String email, String password, List<String> roles,String type,
                   String nom, String prenom, String adresse, String telephone, LocalDate dateNaissance) {
        super(id, email, password, roles, nom, prenom, type);
        this.adresse = adresse;
        this.telephone = telephone;
        this.dateNaissance = dateNaissance;
    }

    /*@ pure @*/
    public String getAdresse() {
        return adresse;
    }

    /*@ assignable this.adresse; @*/
    public void setAdresse(String adresse) {
        this.adresse = adresse;
    }

    /*@ pure @*/
    public String getTelephone() {
        return telephone;
    }

    /*@ assignable this.telephone; @*/
    public void setTelephone(String telephone) {
        this.telephone = telephone;
    }

    /*@ pure @*/
    public LocalDate getDateNaissance() {
        return dateNaissance;
    }

    /*@ 
      @ assignable this.dateNaissance;
      @ ensures this.dateNaissance == dateNaissance;
      @*/
    public void setDateNaissance(LocalDate dateNaissance) {
        this.dateNaissance = dateNaissance;
    }


    @Override
    public String toString() {
        return "Patient{" +
                "id=" + getId() +
                ", email='" + getEmail() + '\'' +
                ", nom='" + getNom() + '\'' +
                ", prenom='" + getPrenom() + '\'' +
                ", roles=" + getRoles() +
                ", adresse='" + adresse + '\'' +
                ", telephone='" + telephone + '\'' +
                ", dateNaissance=" + dateNaissance +
                '}';
    }
}
