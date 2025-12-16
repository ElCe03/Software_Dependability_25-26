package service;

import entite.Patient;
import entite.Users;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mindrot.jbcrypt.BCrypt;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import java.util.List;
import java.sql.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class UserServiceTest {

    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPstmt;
    @Mock
    private ResultSet mockRs;

    private UserService userService;

    @BeforeEach
    void setUp() throws SQLException {
        userService = new UserService(() -> mockConnection);
    }

    @Test
    void testAuthenticate_Success_Patient() throws Exception {
        String email = "test@test.com";
        String password = "password123";
        String hashedPassword = BCrypt.hashpw(password, BCrypt.gensalt());

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true); 
        
        when(mockRs.getString("password")).thenReturn(hashedPassword);
        when(mockRs.getString("type")).thenReturn("PATIENT");
        when(mockRs.getInt("id")).thenReturn(1);
        when(mockRs.getString("nom")).thenReturn("Mario");
        when(mockRs.getString("prenom")).thenReturn("Rossi");
        when(mockRs.getString("email")).thenReturn(email);
        when(mockRs.getString("roles")).thenReturn("[\"ROLE_PATIENT\"]");
        
        when(mockRs.getString("adresse")).thenReturn("Via Roma 1");
        when(mockRs.getString("telephone")).thenReturn("123456789");
        when(mockRs.getDate("date_naissance")).thenReturn(Date.valueOf("1990-01-01"));

        Users result = userService.authenticate(email, password);

        assertNotNull(result, "L'utente non dovrebbe essere null");
        assertTrue(result instanceof Patient, "L'utente dovrebbe essere un Patient");
        assertEquals("Mario", result.getNom());
        assertEquals(email, result.getEmail());
        assertEquals("PATIENT", result.getType());
        
        verify(mockPstmt).setString(1, email); 
    }

    @Test
    void testAuthenticate_WrongPassword() throws Exception {
        String email = "test@test.com";
        String correctHash = BCrypt.hashpw("passwordCorrect", BCrypt.gensalt());
        
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);
        when(mockRs.getString("password")).thenReturn(correctHash);

        Users result = userService.authenticate(email, "passwordSbagliata");

        assertNull(result, "L'autenticazione deve fallire con password errata");
    }

    @Test
    void testAuthenticate_UserNotFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(false); 

        Users result = userService.authenticate("email@inesistente.com", "pass");

        assertNull(result, "Deve ritornare null se l'utente non esiste");
    }

    @Test
    void testAjouterUtilisateur_Patient() throws Exception {
        Patient newPatient = new Patient();
        newPatient.setNom("Luigi");
        newPatient.setPrenom("Verdi");
        newPatient.setEmail("luigi@test.com");
        newPatient.setPassword("password123");
        newPatient.setAdresse("Via Milano");
        newPatient.setTelephone("987654321");
        
        when(mockConnection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS))).thenReturn(mockPstmt);
        ResultSet mockGeneratedKeys = mock(ResultSet.class);
        when(mockPstmt.getGeneratedKeys()).thenReturn(mockGeneratedKeys);
        when(mockGeneratedKeys.next()).thenReturn(true);
        when(mockGeneratedKeys.getInt(1)).thenReturn(55); 

        userService.ajouterUtilisateur(newPatient, "PATIENT");

        assertEquals(55, newPatient.getId());
        assertEquals("PATIENT", newPatient.getType());
        assertTrue(newPatient.getRoles().contains("ROLE_PATIENT"));
        verify(mockPstmt).executeUpdate();
        verify(mockPstmt).setString(eq(4), argThat(arg -> arg.startsWith("$2a$"))); 
    }
    
    @Test
    void testAjouterUtilisateur_ValidationFails() {
        Users emptyUser = new Users();
        
        assertThrows(IllegalArgumentException.class, () -> {
            userService.ajouterUtilisateur(emptyUser, "ADMIN");
        });
    }

    @Test
    void testAuthenticate_Success_Medecin() throws Exception {
        String email = "doc@test.com";
        String password = "pass";
        String hash = BCrypt.hashpw(password, BCrypt.gensalt());

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);
        
        when(mockRs.getInt("id")).thenReturn(10);
        when(mockRs.getString("nom")).thenReturn("Dottore");
        when(mockRs.getString("prenom")).thenReturn("Rossi");
        when(mockRs.getString("email")).thenReturn(email);
        
        when(mockRs.getString("password")).thenReturn(hash);
        when(mockRs.getString("type")).thenReturn("MEDECIN"); 
        when(mockRs.getString("roles")).thenReturn("[\"ROLE_MEDECIN\"]");
        
        when(mockRs.getString("specialite")).thenReturn("Cardiologie");
        when(mockRs.getString("telephone")).thenReturn("111222333");

        Users result = userService.authenticate(email, password);

        assertNotNull(result);
        assertTrue(result instanceof entite.Medecin, "Dovrebbe essere un'istanza di Medecin");
        assertEquals("Cardiologie", ((entite.Medecin) result).getSpecialite());
    }

    @Test
    void testSupprimer_Success() throws Exception {
        when(mockConnection.prepareStatement(contains("SELECT COUNT"))).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);
        when(mockRs.getInt(1)).thenReturn(1); 

        PreparedStatement mockDeleteStmt = mock(PreparedStatement.class);
        when(mockConnection.prepareStatement(startsWith("DELETE"))).thenReturn(mockDeleteStmt);

        userService.supprimer(10);

        verify(mockDeleteStmt).executeUpdate(); 
    }

    @Test
    void testSupprimer_UserNotFound() throws Exception {
        when(mockConnection.prepareStatement(contains("SELECT COUNT"))).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);
        when(mockRs.next()).thenReturn(true);
        when(mockRs.getInt(1)).thenReturn(0); 

        userService.supprimer(99);

        verify(mockConnection, never()).prepareStatement(startsWith("DELETE"));
    }

   @Test
    void testListerUtilisateurs() throws Exception {
        when(mockConnection.prepareStatement(contains("SELECT id, nom"))).thenReturn(mockPstmt);
        when(mockPstmt.executeQuery()).thenReturn(mockRs);

        when(mockRs.next()).thenReturn(true, true, false);
        
        when(mockRs.getString("type")).thenReturn("PATIENT", "STAFF");
        when(mockRs.getInt("id")).thenReturn(1, 2);
        when(mockRs.getString("nom")).thenReturn("Mario", "Luigi");
        when(mockRs.getString("prenom")).thenReturn("Rossi", "Verdi");
        when(mockRs.getString("email")).thenReturn("mario@test.com", "luigi@test.com");
        when(mockRs.getString("roles")).thenReturn("[\"ROLE_PATIENT\"]", "[\"ROLE_STAFF\"]");

        when(mockRs.getString("adresse")).thenReturn("Via Roma 1"); 
        when(mockRs.getString("telephone")).thenReturn("123456", "987654");
        
        when(mockRs.getDate("date_naissance")).thenReturn(Date.valueOf("1990-01-01"));

        List<Users> list = userService.listerUtilisateurs();

        assertEquals(2, list.size(), "La lista deve contenere 2 utenti");
        assertTrue(list.get(0) instanceof entite.Patient);
        assertTrue(list.get(1) instanceof entite.Staff);
        assertEquals("Mario", list.get(0).getNom());
        assertEquals("Luigi", list.get(1).getNom());
    }

    @Test
    void testUpdateUtilisateur_Success() throws Exception {
        Users userToUpdate = new Users();
        userToUpdate.setId(5);
        userToUpdate.setNom("UpdatedName");
        userToUpdate.setPrenom("UpdatedPrenom");
        userToUpdate.setEmail("update@test.com");
        userToUpdate.setPassword("newPassword123"); 
        userToUpdate.setType("ADMIN");
        userToUpdate.setRoles(List.of("ROLE_ADMIN"));

        when(mockConnection.prepareStatement(contains("UPDATE users"))).thenReturn(mockPstmt);
        when(mockPstmt.executeUpdate()).thenReturn(1); 

        userService.updateUtilisateur(userToUpdate);

        verify(mockPstmt).setString(1, "UpdatedName");
        verify(mockPstmt).setString(eq(4), argThat(arg -> arg.startsWith("$2a$")));
    }
    
    @Test
    void testUpdateUtilisateur_Fail_NoId() {
         Users user = new Users();
         user.setId(0); 
         
         assertThrows(IllegalArgumentException.class, () -> userService.updateUtilisateur(user));
    }

    @Test
    void testListerUtilisateurs_SQLException() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB Down"));

        assertThrows(SQLException.class, () -> userService.listerUtilisateurs());
    }

}