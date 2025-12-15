package service;

import entite.User;
import util.DataSource;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class UserServiceE {
    private Connection connection;
    
    // 1. Costruttore STANDARD (usato dall'applicazione)
    public UserServiceE() {
        connection = DataSource.getInstance().getConnection();
    }
    
    // 2. Costruttore per i TEST (usato da UserServiceETest)
    public UserServiceE(Connection connection) {
        this.connection = connection;
    }
    
    public boolean ajouterUser(User user) {
        String sql = "INSERT INTO users (nom, prenom, email, telephone, type, adresse, date_naissance, roles, password, specialite) " +
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
            pstmt.setString(1, user.getNom());
            pstmt.setString(2, user.getPrenom());
            pstmt.setString(3, user.getEmail());
            pstmt.setString(4, user.getTelephone());
            pstmt.setString(5, user.getType());
            pstmt.setString(6, user.getAdresse());
            
            if (user.getDateNaissance() != null) {
                pstmt.setDate(7, Date.valueOf(user.getDateNaissance()));
            } else {
                pstmt.setNull(7, Types.DATE);
            }
            
            String rolesJson = convertRolesToJson(user.getRoles());
            pstmt.setString(8, rolesJson);
            
            pstmt.setString(9, user.getPassword());
            pstmt.setString(10, user.getSpecialite());
            
            int affectedRows = pstmt.executeUpdate();
            
            if (affectedRows > 0) {
                try (ResultSet generatedKeys = pstmt.getGeneratedKeys()) {
                    if (generatedKeys.next()) {
                        user.setId(generatedKeys.getInt(1));
                    }
                }
                return true;
            }
        } catch (SQLException e) {
            System.err.println("Erreur ajout: " + e.getMessage());
            e.printStackTrace();
        }
        return false;
    }
    
    public boolean modifierUser(User user) {
        String sql = "UPDATE users SET nom = ?, prenom = ?, email = ?, telephone = ?, " +
                "type = ?, adresse = ?, date_naissance = ?, roles = ?, password = ?, specialite = ? WHERE id = ?";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setString(1, user.getNom());
            pstmt.setString(2, user.getPrenom());
            pstmt.setString(3, user.getEmail());
            pstmt.setString(4, user.getTelephone());
            pstmt.setString(5, user.getType());
            pstmt.setString(6, user.getAdresse());
            
            if (user.getDateNaissance() != null) {
                pstmt.setDate(7, Date.valueOf(user.getDateNaissance()));
            } else {
                pstmt.setNull(7, Types.DATE);
            }
            
            String rolesJson = convertRolesToJson(user.getRoles());
            pstmt.setString(8, rolesJson);
            pstmt.setString(9, user.getPassword());
            pstmt.setString(10, user.getSpecialite());
            pstmt.setInt(11, user.getId());
            
            return pstmt.executeUpdate() > 0;
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return false;
    }
    
    public boolean supprimerUser(int userId) {
        String sql = "DELETE FROM users WHERE id = ?";
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, userId);
            return pstmt.executeUpdate() > 0;
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return false;
    }
    
    public User recupererUserParId(int userId) {
        String sql = "SELECT * FROM users WHERE id = ?";
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, userId);
            try (ResultSet rs = pstmt.executeQuery()) {
                if (rs.next()) {
                    return extractUserFromResultSet(rs);
                }
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return null;
    }
    
    public List<User> recupererTousUsers() {
        List<User> users = new ArrayList<>();
        String sql = "SELECT * FROM users";
        try (Statement stmt = connection.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            while (rs.next()) {
                users.add(extractUserFromResultSet(rs));
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return users;
    }

    public List<User> recupererUsersParRole(String type) {
        List<User> users = new ArrayList<>();
        String sql = "SELECT * FROM users WHERE type = ?";
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setString(1, type);
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    users.add(extractUserFromResultSet(rs));
                }
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return users;
    }
    
    private String convertRolesToJson(List<String> roles) {
        if (roles == null || roles.isEmpty()) return "[]";
        StringBuilder sb = new StringBuilder("[");
        for (int i = 0; i < roles.size(); i++) {
            sb.append("\"").append(roles.get(i)).append("\"");
            if (i < roles.size() - 1) sb.append(",");
        }
        sb.append("]");
        return sb.toString();
    }
    
    private List<String> convertJsonToRoles(String rolesJson) {
        List<String> roles = new ArrayList<>();
        if (rolesJson != null && !rolesJson.isEmpty()) {
            try {
                String cleanJson = rolesJson.replace("[", "").replace("]", "").replace("\"", "");
                if (!cleanJson.isEmpty()) {
                    String[] roleArray = cleanJson.split(",");
                    for (String role : roleArray) roles.add(role.trim());
                }
            } catch (Exception e) { e.printStackTrace(); }
        }
        return roles;
    }
    
    private User extractUserFromResultSet(ResultSet rs) throws SQLException {
        User user = new User();
        user.setId(rs.getInt("id"));
        user.setNom(rs.getString("nom"));
        user.setPrenom(rs.getString("prenom"));
        user.setEmail(rs.getString("email"));
        user.setPassword(rs.getString("password"));
        user.setTelephone(rs.getString("telephone"));
        user.setType(rs.getString("type") != null ? rs.getString("type") : "");
        user.setAdresse(rs.getString("adresse"));
        
        try { user.setSpecialite(rs.getString("specialite")); } catch (SQLException e) {}
        
        Date sqlDate = rs.getDate("date_naissance");
        if (sqlDate != null) user.setDateNaissance(sqlDate.toLocalDate());
        
        user.setRoles(convertJsonToRoles(rs.getString("roles")));
        return user;
    }
}
