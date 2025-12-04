package entite;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

/**
 * Represents a user in the system who can be either a patient or a medical professional
 */
public class User {
    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String email;
    /*@ spec_public nullable @*/ private String password;

    /*@ spec_public non_null @*/
    private List<String> roles;

    /*@ spec_public nullable @*/ private String nom;
    /*@ spec_public nullable @*/ private String prenom;
    /*@ spec_public nullable @*/ private String type; // "patient", "medecin", etc.
    /*@ spec_public nullable @*/ private String specialite; // only for medecins
    /*@ spec_public nullable @*/ private String telephone;
    /*@ spec_public nullable @*/ private String adresse;
    /*@ spec_public nullable @*/ private LocalDate dateNaissance;
    
    /*@ public invariant roles != null; @*/
    /*@ public invariant (\forall int i; 0 <= i && i < roles.size(); roles.get(i) != null); @*/
    /*@ public invariant id >= 0; @*/

    /*@ 
      @ ensures roles != null && roles.isEmpty();
      @*/
    // Default constructor
    public User() {
        this.roles = new ArrayList<String>();
    }

    /*@ 
      @ requires true; 
      @ 
      @ ensures this.roles != null;
      @ ensures (roles != null) ==> this.roles == roles;
      @ ensures (roles == null) ==> this.roles.isEmpty();
      @*/
    // Parameterized constructor
    public User(String email, String password, List<String> roles, String nom, String prenom, 
                String type, String specialite, String telephone, String adresse, LocalDate dateNaissance) {
        this.email = email;
        this.password = password;
        this.roles = roles != null ? roles : new ArrayList<String>();
        this.nom = nom;
        this.prenom = prenom;
        this.type = type;
        this.specialite = specialite;
        this.telephone = telephone;
        this.adresse = adresse;
        this.dateNaissance = dateNaissance;
    }
    
    // Getters and Setters
    
    /*@ ensures \result == id; pure @*/    
    public int getId() {
        return id;
    }
    
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }
    
    public String getEmail() {
        return email;
    }
    
    public void setEmail(String email) {
        this.email = email;
    }
    
    public String getPassword() {
        return password;
    }
    
    public void setPassword(String password) {
        this.password = password;
    }

    /*@ 
      @ ensures \result != null;
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
    
    /*@ 
      @ requires role != null;
      @ ensures roles.contains(role);
      @ ensures roles.size() == \old(roles.size()) + 1;
      @*/
    public void addRole(String role) {
        if (this.roles == null) {
            this.roles = new ArrayList<String>();
        }
        this.roles.add(role);
    }
    
    public String getNom() {
        return nom;
    }
    
    public void setNom(String nom) {
        this.nom = nom;
    }
    
    public String getPrenom() {
        return prenom;
    }
    
    public void setPrenom(String prenom) {
        this.prenom = prenom;
    }
    
    public String getType() {
        return type;
    }
    
    public void setType(String type) {
        this.type = type;
    }
    
    public String getSpecialite() {
        return specialite;
    }
    
    public void setSpecialite(String specialite) {
        this.specialite = specialite;
    }
    
    public String getTelephone() {
        return telephone;
    }
    
    public void setTelephone(String telephone) {
        this.telephone = telephone;
    }
    
    public String getAdresse() {
        return adresse;
    }
    
    public void setAdresse(String adresse) {
        this.adresse = adresse;
    }
    
    public LocalDate getDateNaissance() {
        return dateNaissance;
    }
    
    public void setDateNaissance(LocalDate dateNaissance) {
        this.dateNaissance = dateNaissance;
    }
    
    /*@ 
      @ ensures \result == ("patient".equalsIgnoreCase(type) || (roles != null && roles.contains("ROLE_PATIENT")));
      @ pure
      @*/
    public boolean isPatient() {
        return "patient".equalsIgnoreCase(type) || (roles != null && roles.contains("ROLE_PATIENT"));
    }
    
    /*@ 
      @ pure
      @*/
    public boolean isMedecin() {
        return "medecin".equalsIgnoreCase(type) || "medcin".equalsIgnoreCase(type) || 
               (roles != null && (roles.contains("ROLE_MEDECIN") || roles.contains("ROLE_MEDCIN")));
    }
    
    @Override
    public String toString() {
        return prenom + " " + nom;
    }
} 