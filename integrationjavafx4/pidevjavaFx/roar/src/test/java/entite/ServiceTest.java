package entite;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class ServiceTest {

    @Test
    void testDefaultConstructor() {
        Service service = new Service();

        assertEquals(0, service.getId());
        assertEquals(0, service.getDuration());
        assertNull(service.getName());
        assertNull(service.getDescription());
    }

    @Test
    void testParameterizedConstructor() {
        String name = "Consultation";
        String description = "General Checkup";
        int duration = 30;

        Service service = new Service(name, description, duration);

        assertEquals(0, service.getId());
        assertEquals(name, service.getName());
        assertEquals(description, service.getDescription());
        assertEquals(duration, service.getDuration());
    }

    @Test
    void testSettersAndGetters() {
        Service service = new Service();

        service.setId(10);
        service.setName("MRI Scan");
        service.setDescription("Full body scan");
        service.setDuration(90);

        assertEquals(10, service.getId());
        assertEquals("MRI Scan", service.getName());
        assertEquals("Full body scan", service.getDescription());
        assertEquals(90, service.getDuration());
    }

    @Test
    void testDurationBoundary() {
        Service service = new Service();
        
        service.setDuration(0);
        assertEquals(0, service.getDuration());
        
        service.setDuration(120);
        assertEquals(120, service.getDuration());
    }

    @Test
    void testToStringFormat() {
        Service service = new Service("Therapy", "Physio", 60);
        service.setId(5);

        String result = service.toString();

        assertNotNull(result);
        assertTrue(result.contains("id=5"));
        assertTrue(result.contains("name='Therapy'"));
        assertTrue(result.contains("duration=60 minutes"));
    }

    @Test
    void testNullableFields() {
        Service service = new Service(null, null, 15);

        assertNull(service.getName());
        assertNull(service.getDescription());
        assertEquals(15, service.getDuration());
    }
}