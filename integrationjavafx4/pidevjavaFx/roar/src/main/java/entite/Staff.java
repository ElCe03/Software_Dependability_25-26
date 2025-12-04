package entite;
import jakarta.persistence.DiscriminatorValue;
import jakarta.persistence.Entity;

import java.util.List;
@Entity
@DiscriminatorValue("STAFF")
public class Staff extends Users{

    /*@ spec_public nullable @*/
    private String telephone;

    /*@ 
      @ ensures roles != null && roles.isEmpty();
      @ ensures telephone == null;
      @*/
    public Staff() {
        super();
    }

    /*@ 
      @ requires roles != null ==> (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null);
      @ 
      @ ensures this.id == id;
      @ ensures this.email == email;
      @ ensures this.telephone == telephone;
      @ ensures (roles != null) ==> this.roles == roles;
      @ ensures (roles == null) ==> (this.roles != null && this.roles.isEmpty());
      @*/
    public Staff(int id, String email, String password, List<String> roles,String type,
                 String nom, String prenom, String telephone) {
        super(id, email, password, roles, nom, prenom, type);
        this.telephone = telephone;
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
        return "Staff{" +
                "id=" + getId() +
                ", email='" + getEmail() + '\'' +
                ", nom='" + getNom() + '\'' +
                ", prenom='" + getPrenom() + '\'' +
                ", roles=" + getRoles() +
                ", telephone='" + telephone + '\'' +
                '}';
    }

}
