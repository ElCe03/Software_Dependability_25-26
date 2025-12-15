package service;

import entite.User;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.sql.*;
import java.time.LocalDate;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class UserServiceETest {

    @Mock
    Connection connection;

    @Mock
    PreparedStatement preparedStatement;

    @Mock
    Statement statement;

    @Mock
    ResultSet resultSet;

    private UserServiceE userService;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);
        // Utilizziamo il costruttore che accetta la connessione Mock
        userService = new UserServiceE(connection);
    }

    @Test
    void testAjouterUser_Success() throws Exception {
        User user = new User();
        user.setNom("Test");
        user.setPrenom("User");
        user.setEmail("test@email.com");
        user.setTelephone("123456");
        user.setType("patient");
        user.setAdresse("Tunis");
        user.setDateNaissance(LocalDate.of(2000, 1, 1));
        user.setRoles(Arrays.asList("ROLE_USER"));
        user.setPassword("pass");
        user.setSpecialite("N/A"); // Assicuriamoci che non sia null per evitare problemi

        // Quando viene preparata una query con RETURN_GENERATED_KEYS
        when(connection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(preparedStatement);
        
        // Configura il comportamento del PreparedStatement
        when(preparedStatement.executeUpdate()).thenReturn(1);
        when(preparedStatement.getGeneratedKeys()).thenReturn(resultSet);
        
        // Configura il ResultSet delle chiavi generate
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt(1)).thenReturn(10); // Simula che l'ID generato sia 10

        boolean result = userService.ajouterUser(user);

        assertTrue(result, "Il metodo dovrebbe restituire true");
        assertEquals(10, user.getId(), "L'ID dell'utente dovrebbe essere aggiornato a 10");
        verify(preparedStatement, times(1)).executeUpdate();
    }

    @Test
    void testModifierUser_Success() throws Exception {
        User user = new User();
        user.setId(1);
        user.setNom("NouveauNom");
        user.setPrenom("Prenom");
        user.setEmail("email@test.com");
        user.setTelephone("555");
        user.setType("medecin");
        user.setAdresse("Centre");
        user.setDateNaissance(LocalDate.of(1995, 5, 5));
        user.setRoles(Collections.singletonList("ROLE_ADMIN"));
        user.setPassword("pwd");
        user.setSpecialite("Cardio");

        // Per l'update usiamo prepareStatement semplice (senza generated keys)
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean updated = userService.modifierUser(user);

        assertTrue(updated, "La modifica dovrebbe restituire true");
        verify(preparedStatement, times(1)).executeUpdate();
    }

    @Test
    void testSupprimerUser_Success() throws Exception {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean deleted = userService.supprimerUser(1);

        assertTrue(deleted, "L'eliminazione dovrebbe restituire true");
        verify(preparedStatement, times(1)).executeUpdate();
    }

    @Test
    void testRecupererUserParId_Success() throws Exception {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt("id")).thenReturn(1);
        when(resultSet.getString("nom")).thenReturn("Ali");
        when(resultSet.getString("prenom")).thenReturn("Test");
        when(resultSet.getString("email")).thenReturn("ali@test.com");
        when(resultSet.getString("password")).thenReturn("pass");
        when(resultSet.getString("telephone")).thenReturn("999");
        when(resultSet.getString("type")).thenReturn("patient");
        when(resultSet.getString("specialite")).thenReturn("Cardiologie"); 
        when(resultSet.getString("adresse")).thenReturn("Tunis");
        when(resultSet.getDate("date_naissance")).thenReturn(Date.valueOf("2000-01-01"));
        when(resultSet.getString("roles")).thenReturn("[\"ROLE_USER\"]");

        User user = userService.recupererUserParId(1);

        assertNotNull(user, "L'utente non dovrebbe essere null");
        assertEquals("Ali", user.getNom());
        assertEquals("patient", user.getType());
        assertEquals("Cardiologie", user.getSpecialite());
    }
}
