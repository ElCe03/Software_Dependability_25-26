package entite;

/**
 * Represents a basic medical service entity
 */
public class Service {

    /*@ spec_public @*/ private int id;
    /*@ spec_public nullable @*/ private String name;
    /*@ spec_public nullable @*/ private String description;
    /*@ spec_public @*/ private int duration; // Using int to store duration (e.g., 90 for 90 minutes)

    /*@ public invariant id >= 0; @*/

    /*@ public invariant duration >= 0; @*/


    /*@ 
      @ ensures id == 0;
      @ ensures duration == 0;
      @*/
    // Default constructor
    public Service() {
    }

    /*@ 
      @ requires duration >= 0;
      @ 
      @ ensures this.name == name;
      @ ensures this.description == description;
      @ ensures this.duration == duration;
      @*/
    // Parameterized constructor
    public Service(String name, String description, int duration) {
        this.name = name;
        this.description = description;
        this.duration = duration; // Duration is now an int
    }

    /*@ ensures \result == id; pure @*/
    // Getters and Setters
    public int getId() {
        return id;
    }

    /*@ 
      @ requires id >= 0; 
      @ assignable this.id; 
      @ ensures this.id == id; 
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ pure @*/
    public String getName() {
        return name;
    }

    /*@ assignable this.name; @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ pure @*/
    public String getDescription() {
        return description;
    }

    /*@ assignable this.description; @*/
    public void setDescription(String description) {
        this.description = description;
    }

    /*@ ensures \result == duration; pure @*/
    public int getDuration() {
        return duration;
    }

    /*@ 
      @ requires duration >= 0;
      @ assignable this.duration;
      @ ensures this.duration == duration;
      @*/
    public void setDuration(int duration) {
        this.duration = duration; // Set duration as an int
    }

    @Override
    public String toString() {
        return "Service{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", duration=" + duration + " minutes" + // Display duration in minutes
                '}';
    }
}
