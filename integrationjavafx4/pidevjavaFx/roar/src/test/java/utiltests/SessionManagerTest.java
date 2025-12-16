package util;

import entite.User;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;

import static org.junit.jupiter.api.Assertions.*;

class SessionManagerTest {

    private User createMockUser(String type, String nom) {
        User u = new User();
        u.setType(type);
        u.setNom(nom);
        u.setPrenom("Test");
        u.setEmail("test@example.com");
        return u;
    }

    @BeforeEach
    void setUp() {
        SessionManager.logout();
    }

    @AfterEach
    void tearDown() {
        SessionManager.logout();
    }

    @Test
    @DisplayName("Verifica l'utente di default all'avvio")
    void testDefaultInitialization() {
        User current = SessionManager.getCurrentUser();
        
        assertNotNull(current, "L'utente corrente non deve mai essere null");
        assertEquals("Dupont", current.getNom());
        assertEquals("Jean", current.getPrenom());
        assertEquals("patient", current.getType());
        
        assertTrue(SessionManager.isLoggedIn(), "Deve risultare loggato di default");
        assertTrue(SessionManager.isPatient(), "L'utente default deve essere un paziente");
    }

    @Test
    @DisplayName("Verifica il ciclo di Login e Logout")
    void testLoginAndLogout() {
        User medecin = createMockUser("medecin", "Dr. House");
        SessionManager.login(medecin);

        assertEquals(medecin, SessionManager.getCurrentUser());
        assertTrue(SessionManager.isDoctor());
        assertFalse(SessionManager.isPatient());

        SessionManager.logout();

        User afterLogout = SessionManager.getCurrentUser();
        assertNotEquals(medecin, afterLogout);
        assertEquals("Dupont", afterLogout.getNom());
        assertTrue(SessionManager.isPatient());
    }

    @Test
    @DisplayName("Verifica setCurrentUser con input validi e invalidi")
    void testSetCurrentUser() {
        User admin = createMockUser("admin", "AdminUser");
        
        SessionManager.setCurrentUser(admin);
        assertEquals(admin, SessionManager.getCurrentUser());
        assertTrue(SessionManager.isAdmin());

        Exception exception = assertThrows(IllegalArgumentException.class, () -> {
            SessionManager.setCurrentUser(null);
        });

        assertEquals("Current user cannot be set to null", exception.getMessage());
    }

    @Test
    @DisplayName("Verifica che i ruoli siano case-insensitive")
    void testRoleCaseInsensitivity() {
        User adminCaps = createMockUser("ADMIN", "Boss");
        SessionManager.login(adminCaps);
        assertTrue(SessionManager.isAdmin(), "Deve riconoscere ADMIN come admin");

        User doctorMixed = createMockUser("MeDeCiN", "Doc");
        SessionManager.login(doctorMixed);
        assertTrue(SessionManager.isDoctor(), "Deve riconoscere MeDeCiN come medecin");
    }


    @Test
    @DisplayName("Verifica il ripristino automatico se lo stato interno è null")
    void testInternalNullRecovery() throws Exception {
        Field field = SessionManager.class.getDeclaredField("currentUser");
        field.setAccessible(true);
        field.set(null, null);

        assertNull(field.get(null));

        User recoveredUser = SessionManager.getCurrentUser();

        assertNotNull(recoveredUser, "Il SessionManager dovrebbe aver ricreato l'utente");
        assertEquals("Dupont", recoveredUser.getNom(), "Dovrebbe aver ripristinato l'utente di default");
    }
    
    @Test
    @DisplayName("Verifica mutua esclusività dei ruoli standard")
    void testRolesExclusivity() {
        SessionManager.login(createMockUser("admin", "Adm"));
        
        assertTrue(SessionManager.isAdmin());
        assertFalse(SessionManager.isDoctor());
        assertFalse(SessionManager.isPatient());
    }

    @Test
    @DisplayName("Gestione robusta di un utente con 'type' nullo")
    void testNullTypeSafety() {
        User incompleteUser = new User();
        incompleteUser.setId(50);
        incompleteUser.setNom("Ghost");
        incompleteUser.setType(null);

        SessionManager.login(incompleteUser);

        assertDoesNotThrow(() -> SessionManager.isPatient());
        
        assertFalse(SessionManager.isPatient());
        assertFalse(SessionManager.isDoctor());
        assertFalse(SessionManager.isAdmin());
    }


    @Test
    @DisplayName("Gestione di ruoli non standard")
    void testUnknownRole() {
        User hacker = createMockUser("HACKER", "Mr. Robot");
        SessionManager.login(hacker);

        assertFalse(SessionManager.isPatient(), "Un hacker non è un paziente");
        assertFalse(SessionManager.isDoctor(), "Un hacker non è un dottore");
        assertFalse(SessionManager.isAdmin(), "Un hacker non è un admin");
    }


    @Test
    @DisplayName("Verifica che le modifiche all'oggetto User si riflettano in sessione")
    void testObjectReferenceIntegrity() {
        User mutableUser = createMockUser("patient", "Original Name");
        SessionManager.login(mutableUser);

        mutableUser.setNom("Changed Name");
        mutableUser.setType("admin"); 

        User sessionUser = SessionManager.getCurrentUser();
        
        
        assertEquals("Changed Name", sessionUser.getNom());
        assertTrue(SessionManager.isAdmin(), "Il cambio di ruolo deve essere immediato");
    }

   
    @Test
    @DisplayName("Stress test concorrente su Login/Logout")
    void testConcurrency() throws InterruptedException {
        Thread t1 = new Thread(() -> {
            SessionManager.login(createMockUser("admin", "Thread1"));
        });

        Thread t2 = new Thread(() -> {
            SessionManager.logout(); 
        });

        t1.start();
        t2.start();

        t1.join();
        t2.join();

        User finalState = SessionManager.getCurrentUser();
        assertNotNull(finalState, "Lo stato finale non deve mai essere null, nemmeno dopo race conditions");
        
        boolean isValidState = "Thread1".equals(finalState.getNom()) || "Dupont".equals(finalState.getNom());
        assertTrue(isValidState, "Lo stato finale deve essere coerente (o login avvenuto o logout avvenuto)");
    }
}