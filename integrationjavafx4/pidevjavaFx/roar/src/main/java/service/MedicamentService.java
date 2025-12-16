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

    /*@ spec_public @*/
    private Connection cnx;

    public MedicamentService() {
    }

    public void setConnection(Connection cnx) {
        this.cnx = cnx;
    }

    private Connection getConnection() {
        if (this.cnx == null) {
            this.cnx = DataSource.getInstance().getConnection();
        }
        return this.cnx;
    }

    /*@ 
      @ requires medicament != null;
      @ requires medicament.getId() == 0;
      @ 
      @ ensures medicament.getId() > 0;
      @ 
      @ signals (RuntimeException e) true;
      @*/
    @Override
    public void create(Medicament medicament) {

        String requete = "INSERT INTO medicament (nom_medicament, description_medicament, type_medicament, prix_medicament, quantite_stock, date_entree, date_expiration) "
                + "VALUES (?, ?, ?, ?, ?, ?, ?)";


        try (PreparedStatement pst = getConnection().prepareStatement(requete, Statement.RETURN_GENERATED_KEYS)) {
            pst.setString(1, medicament.getNom_medicament());
            pst.setString(2, medicament.getDescription_medicament());
            pst.setString(3, medicament.getType_medicament());
            pst.setDouble(4, medicament.getPrix_medicament());
            pst.setInt(5, medicament.getQuantite_stock());
            pst.setDate(6, Date.valueOf(medicament.getDate_entree()));
            pst.setDate(7, Date.valueOf(medicament.getDate_expiration()));

            pst.executeUpdate();


            try (ResultSet generatedKeys = pst.getGeneratedKeys()) {
                if (generatedKeys.next()) {
                    medicament.setId(generatedKeys.getInt(1));
                }
            }
        } catch (SQLException e) {
            throw new RuntimeException("Errore durante la creazione del medicinale", e);
        }
    }

    /*@ 
      @ requires medicament != null;
      @ requires medicament.getId() > 0;
      @*/
    @Override
    public void delete(Medicament medicament) {
        String requete = "DELETE FROM medicament WHERE id = ?";
        try (PreparedStatement pst = getConnection().prepareStatement(requete)) {
            pst.setInt(1, medicament.getId());
            pst.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ 
      @ requires medicament != null;
      @ requires medicament.getId() > 0;
      @*/
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
                + "WHERE id = ?";

        try (PreparedStatement pst = getConnection().prepareStatement(requete)) {
            pst.setString(1, medicament.getNom_medicament());
            pst.setString(2, medicament.getDescription_medicament());
            pst.setString(3, medicament.getType_medicament());
            pst.setDouble(4, medicament.getPrix_medicament());
            pst.setInt(5, medicament.getQuantite_stock());
            pst.setDate(6, Date.valueOf(medicament.getDate_entree()));
            pst.setDate(7, Date.valueOf(medicament.getDate_expiration()));
            pst.setInt(8, medicament.getId());

            pst.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException("Echec de la mise à jour", e);
        }
    }

    /*@ 
      @ ensures \result != null;
      @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
      @*/
    @Override
    public List<Medicament> readAll() {
        List<Medicament> list = new ArrayList<Medicament>();
        String requete = "SELECT * FROM medicament";
        try (Statement ste = getConnection().createStatement();
             ResultSet rs = ste.executeQuery(requete)) {

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

    /*@ 
      @ requires id > 0;
      @ ensures \result != null ==> \result.getId() == id;
      @*/
    @Override
    public Medicament readById(int id) {
        String requete = "SELECT * FROM medicament WHERE id = ?";
        try (PreparedStatement pst = getConnection().prepareStatement(requete)) {
            pst.setInt(1, id);
            try (ResultSet rs = pst.executeQuery()) {
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
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return null;
    }

    /*@ 
      @ ensures \result != null;
      @*/
    public Map<String, Integer> getTypeCounts() {
        Map<String, Integer> typeCounts = new HashMap<String, Integer>();
        String query = "SELECT type_medicament, COUNT(*) AS count FROM medicament GROUP BY type_medicament";

        try (Statement stmt = getConnection().createStatement();
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

    /*@ 
      @ ensures \result != null;
      @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
      @*/
    public List<Medicament> getMedicamentsProchesExpiration() {
        List<Medicament> list = new ArrayList<Medicament>();
        String requete = "SELECT * FROM medicament WHERE date_expiration BETWEEN ? AND ?";

        LocalDate today = LocalDate.now();
        LocalDate limitDate = today.plusDays(30);

        try (PreparedStatement pst = getConnection().prepareStatement(requete)) {
            pst.setDate(1, Date.valueOf(today));
            pst.setDate(2, Date.valueOf(limitDate));

            try (ResultSet rs = pst.executeQuery()) {
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
            }
        } catch (SQLException e) {
            throw new RuntimeException("Erreur lors de la récupération des médicaments proches de l'expiration", e);
        }

        return list;
    }
}