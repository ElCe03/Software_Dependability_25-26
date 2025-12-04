package entite;

import java.sql.Date;

public class Consultation {

    /*@ spec_public @*/ private int id;
    /*@ spec_public @*/ private int serviceId;       // For database relationship
    /*@ spec_public nullable @*/ private String serviceName;  // For display purposes
    /*@ spec_public nullable @*/ private Date date;
    /*@ spec_public nullable @*/ private String patientIdentifier;
    /*@ spec_public nullable @*/ private String status;
    /*@ spec_public nullable @*/ private String phoneNumber;

    /*@ public invariant id >= 0; @*/
    /*@ public invariant serviceId >= 0; @*/

    /*@ 
      @ ensures id == 0;
      @ ensures serviceId == 0;
      @ ensures date == null;
      @ ensures status == null;
      @*/
    // Constructors
    public Consultation() {}

    /*@ 
      @ requires serviceId >= 0;
      @ 
      @ ensures this.serviceId == serviceId;
      @ ensures this.date == date;
      @ ensures this.patientIdentifier == patientIdentifier;
      @ ensures this.status == status;
      @ ensures this.phoneNumber == phoneNumber;
      @ ensures this.id == 0;
      @ ensures this.serviceName == null;
      @*/
    public Consultation(int serviceId, Date date, String patientIdentifier,
                        String status, String phoneNumber) {
        this.serviceId = serviceId;
        this.date = date;
        this.patientIdentifier = patientIdentifier;
        this.status = status;
        this.phoneNumber = phoneNumber;
    }

    // Getters and Setters

    /*@ ensures \result == id; pure @*/
    public int getId() { return id; }
    /*@ requires id >= 0; assignable this.id; ensures this.id == id; @*/
    public void setId(int id) { this.id = id; }

    /*@ ensures \result == serviceId; pure @*/
    public int getServiceId() { return serviceId; }
    /*@ 
      @ requires serviceId >= 0; 
      @ assignable this.serviceId; 
      @ ensures this.serviceId == serviceId; 
      @*/
    public void setServiceId(int serviceId) { this.serviceId = serviceId; }

    /*@ pure @*/
    public String getServiceName() { return serviceName; }
    /*@ assignable this.serviceName; @*/
    public void setServiceName(String serviceName) { this.serviceName = serviceName; }

    /*@ pure @*/
    public Date getDate() { return date; }
    /*@ assignable this.date; @*/
    public void setDate(Date date) { this.date = date; }

    /*@ pure @*/
    public String getPatientIdentifier() { return patientIdentifier; }
    /*@ assignable this.patientIdentifier; @*/
    public void setPatientIdentifier(String patientIdentifier) { this.patientIdentifier = patientIdentifier; }

    /*@ pure @*/
    public String getStatus() { return status; }
    /*@ assignable this.status; @*/
    public void setStatus(String status) { this.status = status; }

    /*@ pure @*/
    public String getPhoneNumber() { return phoneNumber; }
    /*@ assignable this.phoneNumber; @*/
    public void setPhoneNumber(String phoneNumber) { this.phoneNumber = phoneNumber; }
}