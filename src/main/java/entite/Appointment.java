package entite;

import java.time.LocalDateTime;

public class Appointment {
    private String title;
    private String description;
    private LocalDateTime start;
    private LocalDateTime end;
    private String group;

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
    public LocalDateTime getStart() { return start; }
    public LocalDateTime getEnd() { return end; }
    public String getGroup() { return group; }

    // Setters
    public void setTitle(String title) { this.title = title; }
    public void setDescription(String description) { this.description = description; }
    public void setStart(LocalDateTime start) { this.start = start; }
    public void setEnd(LocalDateTime end) { this.end = end; }
    public void setGroup(String group) { this.group = group; }
} 