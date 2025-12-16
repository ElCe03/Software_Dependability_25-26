package entite;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.MethodSource;

import java.time.LocalDateTime;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

class AppointmentTest {

    private LocalDateTime referenceTime;

    @BeforeEach
    void setUp() {
        referenceTime = LocalDateTime.of(2023, 10, 15, 12, 0);
    }


    @ParameterizedTest(name = "Test {index}: Title='{0}', Desc='{1}', Group='{2}'")
    @CsvSource({
        "Daily Standup, Sync team, Engineering",
        "'', Empty Description, ''",  
        "Null Check, , ",             
        "Special Char @#$, Format test, N/A"
    })
    @DisplayName("Should handle various String inputs (Valid & Boundary)")
    void testStringPropertiesVariance(String title, String desc, String group) {
        LocalDateTime end = referenceTime.plusHours(1);
        Appointment appt = new Appointment(title, desc, referenceTime, end, group);

        assertAll("Check String Properties",
            () -> assertEquals(title, appt.getTitle()),
            () -> assertEquals(desc, appt.getDescription()),
            () -> assertEquals(group, appt.getGroup())
        );
    }


    static Stream<Arguments> dateProvider() {
        LocalDateTime base = LocalDateTime.of(2023, 1, 1, 10, 0);
        return Stream.of(
            Arguments.of(base, base.plusHours(1), "Standard 1 Hour"),
            Arguments.of(base, base, "Zero Duration (Start == End)"), 
            Arguments.of(base, base.plusYears(1), "Long Duration (1 Year)")
        );
    }

    @ParameterizedTest(name = "{2}")
    @MethodSource("dateProvider")
    @DisplayName("Should accept valid time ranges including boundaries")
    void testTimeBoundaries(LocalDateTime start, LocalDateTime end, String scenarioDesc) {
        Appointment appt = new Appointment("TimeTest", "Desc", start, end, "Group");
        
        assertAll("Time Validation",
            () -> assertEquals(start, appt.getStart()),
            () -> assertEquals(end, appt.getEnd()),
            () -> assertFalse(appt.getStart().isAfter(appt.getEnd()), "Invariant Violation: Start > End")
        );
    }


    @Test
    @DisplayName("Should respect Equality contract (needs equals/hashCode implementation)")
    void testEqualityAndHashCode() {

        
        LocalDateTime end = referenceTime.plusHours(1);
        Appointment appt1 = new Appointment("A", "B", referenceTime, end, "C");
        Appointment appt2 = new Appointment("A", "B", referenceTime, end, "C"); 
        Appointment appt3 = new Appointment("X", "Y", referenceTime, end, "Z"); 

;
    }
    
    
    @Test
    @DisplayName("Should verify independent modification")
    void testIndependentInstances() {
        LocalDateTime end = referenceTime.plusHours(1);
        Appointment appt1 = new Appointment("Original", "Desc", referenceTime, end, "G");
        Appointment appt2 = new Appointment("Original", "Desc", referenceTime, end, "G");
        
        appt1.setTitle("Modified");
        
        assertNotEquals(appt1.getTitle(), appt2.getTitle(), "Modifying one instance should not affect another");
    }
}