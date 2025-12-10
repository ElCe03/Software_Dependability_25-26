package entite;
import java.util.ArrayList;
import java.util.List;
import jakarta.persistence.*;
@Entity
@Table(name = "user") // le nom de ta table en base
@Inheritance(strategy = InheritanceType.SINGLE_TABLE)
@DiscriminatorColumn(name = "role_type", discriminatorType = DiscriminatorType.STRING)


public class Users {
    /*@ spec_public @*/
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;

    /*@ spec_public nullable @*/
    @Column(nullable = false, unique = true)
    private String email;

    /*@ spec_public nullable @*/
    private String password;
    
    /*@ spec_public non_null @*/
    @ElementCollection(fetch = FetchType.EAGER)
    private List<String> roles = new ArrayList<String>();
    /*@ spec_public nullable @*/
    private String nom;

    /*@ spec_public nullable @*/
    private String prenom;

    /*@ spec_public nullable @*/
    private String type;

    /*@ public invariant roles != null; @*/
    /*@ public invariant (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null); @*/
    /*@ public invariant id >= 0; @*/

    /*@ 
      @ // Garantisce che dopo la creazione, la lista ruoli sia inizializzata (non null) ma vuota.
      @ ensures roles != null && roles.isEmpty();
      @ ensures id == 0;
      @*/
    public Users() {
        this.roles = new ArrayList<String>();
    }

    /*@ 
      @ requires roles != null ==> (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null);
      @ 
      @ ensures this.id == id;
      @ ensures this.email == email;
      @ ensures this.type == type;
      @ 
      @ ensures (roles != null) ==> this.roles == roles;
      @ ensures (roles == null) ==> (this.roles != null && this.roles.isEmpty());
      @*/
    public Users(int id, String email, String password, List<String> roles, String nom, String prenom, String type) {
        this.id = id;
        this.email = email;
        this.password = password;
        this.roles = roles != null ? roles : new ArrayList<String>();
        this.nom = nom;
        this.prenom = prenom;
        this.type = type;
    }

    /*@ 
      @ ensures roles != null; // Garantito dall'inizializzazione del campo
      @*/
    public Users(int i, String dupont, String jean, String mail, String roleMedecin, String médecin) {

    }

    /*@ ensures \result == id; pure @*/
    public int getId() {
        return id;
    }

    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ ensures \result == email; pure @*/
    public String getEmail() {
        return email;
    }

    /*@ assignable this.email; ensures this.email == email; @*/
    public void setEmail(String email) {
        this.email = email;
    }

    /*@ ensures \result == password; pure @*/
    public String getPassword() {
        return password;
    }

    /*@ assignable this.password; ensures this.password == password; @*/
    public void setPassword(String password) {
        this.password = password;
    }

    /*@ 
      @ ensures \result != null; // Garanzia fondamentale per i client
      @ ensures \result == roles; 
      @ pure 
      @*/
    public List<String> getRoles() {
        return roles;
    }

    /*@ 
      @ requires roles != null;
      @ assignable this.roles;
      @ ensures this.roles == roles;
      @*/
    public void setRoles(List<String> roles) {
        this.roles = roles;
    }

    /*@ ensures \result == nom; pure @*/
    public String getNom() {
        return nom;
    }

    /*@ assignable this.nom; ensures this.nom == nom; @*/
    public void setNom(String nom) {
        this.nom = nom;
    }

    /*@ ensures \result == prenom; pure @*/
    public String getPrenom() {
        return prenom;
    }

    /*@ assignable this.prenom; ensures this.prenom == prenom; @*/
    public void setPrenom(String prenom) {
        this.prenom = prenom;
    }

    /*@ ensures \result == type; pure @*/
    public String getType() {
        return type;
    }

    /*@ assignable this.type; ensures this.type == type; @*/
    public void setType(String type) {
        this.type = type;
    }
    
    @Override
    public String toString() {
        return "User{" +
                "id=" + id +
                ", email='" + email + '\'' +
                ", nom='" + nom + '\'' +
                ", prenom='" + prenom + '\'' +
                ", roles=" + roles +
                '}';
    }
}
