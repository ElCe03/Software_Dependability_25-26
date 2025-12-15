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

    @Mock Connection connection;
    @Mock PreparedStatement preparedStatement;
    @Mock Statement statement;
    @Mock ResultSet resultSet;

    private UserServiceE userService;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);
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
        user.setSpecialite("N/A");

        when(connection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);
        when(preparedStatement.getGeneratedKeys()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt(1)).thenReturn(10);

        boolean result = userService.ajouterUser(user);
        assertTrue(result);
        assertEquals(10, user.getId());
    }

    @Test
    void testModifierUser_Success() throws Exception {
        User user = new User();
        user.setId(1);
        user.setNom("Nom");
        user.setPrenom("Pre");
        user.setEmail("e@e.com");
        user.setTelephone("111");
        user.setType("medecin");
        user.setAdresse("Add");
        user.setDateNaissance(LocalDate.of(1990, 1, 1));
        user.setRoles(Collections.singletonList("ROLE_ADMIN"));
        user.setPassword("p");
        user.setSpecialite("Cardio");

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean updated = userService.modifierUser(user);
        assertTrue(updated);
    }

    @Test
    void testSupprimerUser_Success() throws Exception {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);
        boolean deleted = userService.supprimerUser(1);
        assertTrue(deleted);
    }

    @Test
    void testRecupererUserParId_Success() throws Exception {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt("id")).thenReturn(1);
        when(resultSet.getString("nom")).thenReturn("Ali");
        when(resultSet.getString("type")).thenReturn("patient");
        when(resultSet.getString("specialite")).thenReturn("Cardio");
        when(resultSet.getString("roles")).thenReturn("[\"ROLE_USER\"]");

        User user = userService.recupererUserParId(1);
        assertNotNull(user);
        assertEquals("Ali", user.getNom());
    }
}
