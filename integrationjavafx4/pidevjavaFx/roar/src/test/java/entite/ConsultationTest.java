package entite;

import org.junit.jupiter.api.Test;
import java.sql.Date;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class ConsultationTest {

    @Test
    void testDefaultConstructor() {
        Consultation consultation = new Consultation();

        assertEquals(0, consultation.getId());
        assertEquals(0, consultation.getServiceId());
        assertNull(consultation.getServiceName());
        assertNull(consultation.getDate());
        assertNull(consultation.getPatientIdentifier());
        assertNull(consultation.getStatus());
        assertNull(consultation.getPhoneNumber());
    }

    @Test
    void testParameterizedConstructor() {
        int serviceId = 101;
        Date date = Date.valueOf(LocalDate.of(2023, 12, 25));
        String patientId = "PAT-001";
        String status = "CONFIRMED";
        String phone = "+39000000000";

        Consultation consultation = new Consultation(serviceId, date, patientId, status, phone);

        assertAll(
            () -> assertEquals(serviceId, consultation.getServiceId()),
            () -> assertEquals(date, consultation.getDate()),
            () -> assertEquals(patientId, consultation.getPatientIdentifier()),
            () -> assertEquals(status, consultation.getStatus()),
            () -> assertEquals(phone, consultation.getPhoneNumber()),
            () -> assertEquals(0, consultation.getId()),
            () -> assertNull(consultation.getServiceName())
        );
    }

    @Test
    void testSettersAndGetters() {
        Consultation consultation = new Consultation();

        int id = 50;
        int serviceId = 202;
        String serviceName = "Cardiology";
        Date date = Date.valueOf("2024-01-01");
        String patientId = "XYZ-999";
        String status = "PENDING";
        String phone = "123456789";

        consultation.setId(id);
        consultation.setServiceId(serviceId);
        consultation.setServiceName(serviceName);
        consultation.setDate(date);
        consultation.setPatientIdentifier(patientId);
        consultation.setStatus(status);
        consultation.setPhoneNumber(phone);

        assertAll(
            () -> assertEquals(id, consultation.getId()),
            () -> assertEquals(serviceId, consultation.getServiceId()),
            () -> assertEquals(serviceName, consultation.getServiceName()),
            () -> assertEquals(date, consultation.getDate()),
            () -> assertEquals(patientId, consultation.getPatientIdentifier()),
            () -> assertEquals(status, consultation.getStatus()),
            () -> assertEquals(phone, consultation.getPhoneNumber())
        );
    }

    @Test
    void testDateMutability() {
        Date originalDate = Date.valueOf("2024-05-01");
        Consultation consultation = new Consultation();
        consultation.setDate(originalDate);

        Date fetchedDate = consultation.getDate();
        assertEquals(originalDate.getTime(), fetchedDate.getTime());
    }

    @Test
    void testNullableFieldsStrictness() {
        Consultation consultation = new Consultation();
        
        consultation.setServiceName(null);
        consultation.setPatientIdentifier(null);
        consultation.setStatus(null);
        consultation.setPhoneNumber(null);
        consultation.setDate(null);

        assertAll(
            () -> assertNull(consultation.getServiceName()),
            () -> assertNull(consultation.getPatientIdentifier()),
            () -> assertNull(consultation.getStatus()),
            () -> assertNull(consultation.getPhoneNumber()),
            () -> assertNull(consultation.getDate())
        );
    }
}