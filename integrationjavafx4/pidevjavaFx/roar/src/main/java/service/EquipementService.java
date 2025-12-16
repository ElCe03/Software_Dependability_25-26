package service;

import entite.Equipement;
import util.DataSource;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class EquipementService {
    

    private Connection connection;

    public EquipementService() {
    }

    public void setConnection(Connection connection) {
        this.connection = connection;
    }

    private Connection getConnection() {
        if (this.connection == null) {
            this.connection = DataSource.getInstance().getConnection();
        }
        return this.connection;
    }

    public void ajouterEquipement(Equipement e) {
        String sql = "INSERT INTO equipement (nom, type, statut, category) VALUES (?, ?, ?, ?)";
        try (PreparedStatement pst = getConnection().prepareStatement(sql)) {
            pst.setString(1, e.getNom());
            pst.setString(2, e.getType());
            pst.setString(3, e.getStatut());
            pst.setString(4, e.getCategory());
            pst.executeUpdate();
            System.out.println("✅ Équipement ajouté avec succès !");
        } catch (SQLException ex) {
            System.err.println("❌ Erreur lors de l'ajout de l'équipement : " + ex.getMessage());
        }
    }

    public List<Equipement> getAllEquipements() {
        List<Equipement> result = new ArrayList<Equipement>();
        String sql = "SELECT * FROM equipement";
        try (Statement stmt = getConnection().createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            while (rs.next()) {
                Equipement e = new Equipement(
                        rs.getInt("id"),
                        rs.getString("nom"),
                        rs.getString("type"),
                        rs.getString("statut"),
                        rs.getString("category")
                );
                result.add(e);
            }
        } catch (SQLException ex) {
            System.err.println("❌ Erreur lors de la récupération des équipements : " + ex.getMessage());
        }
        return result;
    }

    public Equipement getEquipementById(int id) {
        String sql = "SELECT * FROM equipement WHERE id = ?";
        try (PreparedStatement ps = getConnection().prepareStatement(sql)) {
            ps.setInt(1, id);
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    return new Equipement(
                            rs.getInt("id"),
                            rs.getString("nom"),
                            rs.getString("type"),
                            rs.getString("statut"),
                            rs.getString("category")
                    );
                }
            }
        } catch (SQLException ex) {
            System.err.println("❌ Erreur lors de la récupération de l'équipement par ID : " + ex.getMessage());
        }
        return null;
    }

    public void updateEquipement(Equipement equipement) {
        String query = "UPDATE equipement SET nom=?, type=?, statut=?, category=? WHERE id=?";
        try (PreparedStatement ps = getConnection().prepareStatement(query)) {
            ps.setString(1, equipement.getNom());
            ps.setString(2, equipement.getType());
            ps.setString(3, equipement.getStatut());
            ps.setString(4, equipement.getCategory());
            ps.setInt(5, equipement.getId());
            int rows = ps.executeUpdate();
            if (rows == 0) {
                System.err.println("❌ Aucune ligne affectée - échec de la mise à jour");
            } else {
                System.out.println("✅ L'équipement a été mis à jour avec succès !");
            }
        } catch (SQLException e) {
            System.err.println("❌ Erreur lors de la mise à jour de l'équipement : " + e.getMessage());
        }
    }

    public void supprimerEquipement(int id) {
        String sql = "DELETE FROM equipement WHERE id=?";
        try (PreparedStatement ps = getConnection().prepareStatement(sql)) {
            ps.setInt(1, id);
            int rows = ps.executeUpdate();
            if (rows == 0) {
                System.err.println("❌ Aucune ligne supprimée - ID introuvable : " + id);
            } else {
                System.out.println("✅ Équipement supprimé avec succès !");
            }
        } catch (SQLException ex) {
            System.err.println("❌ Erreur lors la suppression de l'équipement : " + ex.getMessage());
        }
    }

    public void deleteEquipementAndDependents(int equipementId) {
        String deleteEntretienSql = "DELETE FROM entretien WHERE equipement_id = ?";
        String deleteEquipementSql = "DELETE FROM equipement WHERE id = ?";

        try {
            getConnection().setAutoCommit(false);

            try (PreparedStatement psEntretien = getConnection().prepareStatement(deleteEntretienSql)) {
                psEntretien.setInt(1, equipementId);
                psEntretien.executeUpdate();
            }

            try (PreparedStatement psEquipement = getConnection().prepareStatement(deleteEquipementSql)) {
                psEquipement.setInt(1, equipementId);
                int rows = psEquipement.executeUpdate();
                if (rows == 0) {
                    System.out.println("❌ Aucun équipement trouvé avec l'ID " + equipementId);
                } else {
                    System.out.println("✅ Équipement et ses entretiens supprimés !");
                }
            }

            getConnection().commit();
        } catch (SQLException ex) {
            try {
                if (connection != null) getConnection().rollback();
            } catch (SQLException e) {
                System.err.println("❌ Erreur rollback : " + e.getMessage());
            }
            System.err.println("❌ Erreur lors de la suppression : " + ex.getMessage());
        } finally {
            try {
                if (connection != null) getConnection().setAutoCommit(true);
            } catch (SQLException e) {
                System.err.println("❌ Erreur reset auto-commit : " + e.getMessage());
            }
        }
    }

    public List<Equipement> getEquipementsByCategory(String category) {
        List<Equipement> equipements = new ArrayList<Equipement>();
        String sql = "SELECT * FROM equipement WHERE category = ?";
        try (PreparedStatement ps = getConnection().prepareStatement(sql)) {
            ps.setString(1, category);
            try (ResultSet rs = ps.executeQuery()) {
                while (rs.next()) {
                    Equipement e = new Equipement(
                            rs.getInt("id"),
                            rs.getString("nom"),
                            rs.getString("type"),
                            rs.getString("statut"),
                            rs.getString("category")
                    );
                    equipements.add(e);
                }
            }
        } catch (SQLException ex) {
            System.err.println("❌ Erreur lors de la récupération par catégorie : " + ex.getMessage());
        }
        return equipements;
    }

    public void mettreAJourStatut(Equipement equipement) {
        String sql = "UPDATE equipement SET statut = ? WHERE id = ?";

        try (PreparedStatement stmt = getConnection().prepareStatement(sql)) {
            stmt.setString(1, equipement.getStatut());
            stmt.setInt(2, equipement.getId());

            stmt.executeUpdate();

            System.out.println("✅ Statut mis à jour en '" + equipement.getStatut() + "'");
        } catch (SQLException e) {
            System.err.println("❌ Erreur SQL : " + e.getMessage());
        }
    }

    public void modifierEquipement(Equipement equipement) {
        String sql = "UPDATE equipement SET nom = ?, type = ?, statut = ?, category = ? WHERE id = ?";
        try (PreparedStatement pstmt = getConnection().prepareStatement(sql)) {
            pstmt.setString(1, equipement.getNom());
            pstmt.setString(2, equipement.getType());
            pstmt.setString(3, equipement.getStatut());
            pstmt.setString(4, equipement.getCategory());
            pstmt.setInt(5, equipement.getId());

            pstmt.executeUpdate();
            System.out.println("✅ L'équipement a été mis à jour avec succès !");
        } catch (SQLException e) {
            System.err.println("❌ Erreur lors de la mise à jour de l'équipement : " + e.getMessage());
        }
    }
}