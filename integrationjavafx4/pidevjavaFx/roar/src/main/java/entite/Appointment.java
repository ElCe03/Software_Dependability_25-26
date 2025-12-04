package entite;

import java.time.LocalDateTime;

public class Appointment {

    /*@ spec_public nullable @*/ private String title;
    /*@ spec_public nullable @*/ private String description;
    /*@ spec_public non_null @*/ private LocalDateTime start;
    /*@ spec_public non_null @*/ private LocalDateTime end;
    /*@ spec_public nullable @*/ private String group;

    /*@ public invariant start != null; @*/
    /*@ public invariant end != null; @*/
    /*@ public invariant !start.isAfter(end); @*/

    /*@ 
      @ requires start != null;
      @ requires end != null;
      @ requires !start.isAfter(end);
      @ 
      @ ensures this.start == start;
      @ ensures this.end == end;
      @*/
    public Appointment(String title, String description, LocalDateTime start, LocalDateTime end, String group) {
        this.title = title;
        this.description = description;
        this.start = start;
        this.end = end;
        this.group = group;
    }

    // Getters
    public String getTitle() { return title; }
    public String getDescription() { return description; }
    /*@ ensures \result == start; pure @*/
    public LocalDateTime getStart() { return start; }
    /*@ ensures \result == end; pure @*/
    public LocalDateTime getEnd() { return end; }
    public String getGroup() { return group; }

    // Setters
    public void setTitle(String title) { this.title = title; }
    public void setDescription(String description) { this.description = description; }
    /*@ 
      @ requires start != null;
      @ requires !start.isAfter(this.end);
      @ assignable this.start;
      @ ensures this.start == start;
      @*/
    public void setStart(LocalDateTime start) { this.start = start; }
    /*@ 
      @ requires end != null;
      @ requires !this.start.isAfter(end);
      @ assignable this.end;
      @ ensures this.end == end;
      @*/
    public void setEnd(LocalDateTime end) { this.end = end; }
    public void setGroup(String group) { this.group = group; }
} 