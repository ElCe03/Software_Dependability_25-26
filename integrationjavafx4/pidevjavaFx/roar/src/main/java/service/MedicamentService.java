package service;

import entite.Medicament;
import util.DataSource;

import java.sql.*;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MedicamentService implements IService<Medicament> {

    private Connection cnx;
    private Statement ste;
    private PreparedStatement pst;
    private ResultSet rs;

    public MedicamentService() {
        cnx = DataSource.getInstance().getConnection();
    }

    @Override
    public void create(Medicament medicament) {
        String requete = "INSERT INTO medicament (nom_medicament, description_medicament, type_medicament, prix_medicament, quantite_stock, date_entree, date_expiration) " +
                "VALUES ('" + medicament.getNom_medicament() + "', '" +
                medicament.getDescription_medicament() + "', '" +
                medicament.getType_medicament() + "', " +
                medicament.getPrix_medicament() + ", " +
                medicament.getQuantite_stock() + ", '" +
                medicament.getDate_entree() + "', '" +
                medicament.getDate_expiration() + "')";
        try {
            ste = cnx.createStatement();
            ste.executeUpdate(requete);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }


    public void createPst(Medicament medicament) {
        String requete = "INSERT INTO medicament (nom_medicament, description_medicament, type_medicament, prix_medicament, quantite_stock, date_entree, date_expiration) "
                + "VALUES (?, ?, ?, ?, ?, ?, ?)";

        try (PreparedStatement pst = cnx.prepareStatement(requete, Statement.RETURN_GENERATED_KEYS)) {
            pst.setString(1, medicament.getNom_medicament());
            pst.setString(2, medicament.getDescription_medicament());
            pst.setString(3, medicament.getType_medicament());
            pst.setDouble(4, medicament.getPrix_medicament());
            pst.setInt(5, medicament.getQuantite_stock());
            pst.setDate(6, Date.valueOf(medicament.getDate_entree()));
            pst.setDate(7, Date.valueOf(medicament.getDate_expiration()));

            pst.executeUpdate();

            // Obtenir l'ID généré
            try (ResultSet generatedKeys = pst.getGeneratedKeys()) {
                if (generatedKeys.next()) {
                    medicament.setId(generatedKeys.getInt(1)); // mettre à jour l'objet Java
                }
            }
        } catch (SQLException e) {
            throw new RuntimeException("Échec de la création", e);
        }
    }

    @Override
    public void delete(Medicament medicament) {
        String requete = "DELETE FROM medicament WHERE id = ?";
        try {
            pst = cnx.prepareStatement(requete);
            pst.setInt(1, medicament.getId());
            pst.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void update(Medicament medicament) {
        String requete = "UPDATE medicament SET "
                + "nom_medicament = ?, "
                + "description_medicament = ?, "
                + "type_medicament = ?, "
                + "prix_medicament = ?, "
                + "quantite_stock = ?, "
                + "date_entree = ?, "
                + "date_expiration = ? "
                + "WHERE id = ?"; // 8 paramètres

        try (PreparedStatement pst = cnx.prepareStatement(requete)) {
            pst.setString(1, medicament.getNom_medicament());
            pst.setString(2, medicament.getDescription_medicament());
            pst.setString(3, medicament.getType_medicament());
            pst.setDouble(4, medicament.getPrix_medicament());
            pst.setInt(5, medicament.getQuantite_stock());
            pst.setDate(6, Date.valueOf(medicament.getDate_entree()));
            pst.setDate(7, Date.valueOf(medicament.getDate_expiration()));
            pst.setInt(8, medicament.getId()); // ID en dernier

            pst.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException("Échec de la mise à jour", e);
        }
    }

    @Override
    public List<Medicament> readAll() {
        List<Medicament> list = new ArrayList<>();
        String requete = "SELECT * FROM medicament";
        try {
            ste = cnx.createStatement();
            rs = ste.executeQuery(requete);
            while (rs.next()) {
                list.add(new Medicament(
                        rs.getInt("id"),
                        rs.getString("nom_medicament"),
                        rs.getString("description_medicament"),
                        rs.getString("type_medicament"),
                        rs.getDouble("prix_medicament"),
                        rs.getInt("quantite_stock"),
                        rs.getDate("date_entree").toLocalDate(),
                        rs.getDate("date_expiration").toLocalDate()
                ));
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return list;
    }

    @Override
    public Medicament readById(int id) {
        String requete = "SELECT * FROM medicament WHERE id = ?";
        try {
            pst = cnx.prepareStatement(requete);
            pst.setInt(1, id);
            rs = pst.executeQuery();
            if (rs.next()) {
                return new Medicament(
                        rs.getInt("id"),
                        rs.getString("nom_medicament"),
                        rs.getString("description_medicament"),
                        rs.getString("type_medicament"),
                        rs.getDouble("prix_medicament"),
                        rs.getInt("quantite_stock"),
                        rs.getDate("date_entree").toLocalDate(),
                        rs.getDate("date_expiration").toLocalDate()
                );
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return null;
    }
    public Map<String, Integer> getTypeCounts() {
        Map<String, Integer> typeCounts = new HashMap<>();

        String query = "SELECT type_medicament, COUNT(*) AS count FROM medicament GROUP BY type_medicament";
        try (Statement stmt = cnx.createStatement();
             ResultSet rs = stmt.executeQuery(query)) {

            while (rs.next()) {
                String type = rs.getString("type_medicament");
                int count = rs.getInt("count");
                typeCounts.put(type, count);
            }

        } catch (SQLException e) {
            e.printStackTrace();
        }

        return typeCounts;
    }

    public List<Medicament> getMedicamentsProchesExpiration() {
        List<Medicament> list = new ArrayList<>();
        String requete = "SELECT * FROM medicament WHERE date_expiration BETWEEN ? AND ?";

        LocalDate today = LocalDate.now();
        LocalDate limitDate = today.plusDays(30);

        try (PreparedStatement pst = cnx.prepareStatement(requete)) {
            pst.setDate(1, Date.valueOf(today));
            pst.setDate(2, Date.valueOf(limitDate));

            ResultSet rs = pst.executeQuery();
            while (rs.next()) {
                list.add(new Medicament(
                        rs.getInt("id"),
                        rs.getString("nom_medicament"),
                        rs.getString("description_medicament"),
                        rs.getString("type_medicament"),
                        rs.getDouble("prix_medicament"),
                        rs.getInt("quantite_stock"),
                        rs.getDate("date_entree").toLocalDate(),
                        rs.getDate("date_expiration").toLocalDate()
                ));
            }
        } catch (SQLException e) {
            throw new RuntimeException("Erreur lors de la récupération des médicaments proches de l'expiration", e);
        }

        return list;
    }

}
