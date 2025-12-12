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
        // create service with mocked connection (we added the constructor)
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

        when(connection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);
        when(preparedStatement.getGeneratedKeys()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt(1)).thenReturn(10);

        boolean result = userService.ajouterUser(user);

        assertTrue(result);
        assertEquals(10, user.getId());
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

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean updated = userService.modifierUser(user);

        assertTrue(updated);
        verify(preparedStatement, times(1)).executeUpdate();
    }

    @Test
    void testSupprimerUser_Success() throws Exception {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean deleted = userService.supprimerUser(1);

        assertTrue(deleted);
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
        when(resultSet.getString("specialite")).thenReturn(null);
        when(resultSet.getString("adresse")).thenReturn("Tunis");
        when(resultSet.getDate("date_naissance")).thenReturn(Date.valueOf("2000-01-01"));
        when(resultSet.getString("roles")).thenReturn("[\"ROLE_USER\"]");

        User user = userService.recupererUserParId(1);

        assertNotNull(user);
        assertEquals("Ali", user.getNom());
        assertEquals("patient", user.getType());
    }
}
