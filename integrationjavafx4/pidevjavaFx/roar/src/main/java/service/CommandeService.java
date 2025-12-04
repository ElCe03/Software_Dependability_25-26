package service;

import entite.Commande;
import entite.Medicament;
import entite.MedicamentCommande;
import util.DataSource;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class CommandeService implements IService<Commande> {

    /*@ spec_public non_null @*/
    private Connection cnx = DataSource.getInstance().getConnection();

    /*@ 
      @ requires commande != null;
      @ requires commande.getId() == 0;
      @
      @ ensures commande.getId() > 0;
      @ 
      @ signals (RuntimeException e) true;
      @*/
    @Override
    public void create(Commande commande) {
        String sql = "INSERT INTO commande (date_commande, total_prix, quantite, stripe_session_id, status) VALUES (?, ?, ?, ?, ?)";

        try {
            cnx.setAutoCommit(false);

            try (PreparedStatement pst = cnx.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
                pst.setDate(1, Date.valueOf(commande.getDate_commande()));
                pst.setDouble(2, commande.getTotal_prix());
                pst.setInt(3, commande.getQuantite());
                pst.setString(4, commande.getStripeSessionId());
                pst.setString(5, commande.getStatus() != null ? commande.getStatus() : "pending");
                pst.executeUpdate();

                try (ResultSet rs = pst.getGeneratedKeys()) {
                    if(rs.next()) {
                        commande.setId(rs.getInt(1));
                    }
                }

                saveLignesCommande(commande);
                cnx.commit();
            }
        } catch (SQLException e) {
            try {
                cnx.rollback();
            } catch (SQLException ex) {
                throw new RuntimeException("Erreur lors du rollback", ex);
            }
            throw new RuntimeException("Échec de la création de commande", e);
        } finally {
            try {
                cnx.setAutoCommit(true);
            } catch (SQLException e) {
                e.printStackTrace();
            }
        }
    }

    /*@ 
      @ requires commande != null;
      @ requires commande.getId() > 0;
      @ requires commande.getMedicaments() != null;
      @ signals (SQLException e) true;
      @*/
    private void saveLignesCommande(Commande commande) throws SQLException {
        String sql = "INSERT INTO medicament_commande (commande_id, medicament_id, quantite) VALUES (?, ?, ?)";

        try (PreparedStatement pst = cnx.prepareStatement(sql)) {
            for(MedicamentCommande mc : commande.getMedicaments()) {
                pst.setInt(1, commande.getId());
                pst.setInt(2, mc.getMedicament().getId());
                pst.setInt(3, mc.getQuantite());
                pst.addBatch();
            }
            pst.executeBatch();
        }
    }

    /*@ 
      @ requires commande != null;
      @ requires commande.getId() > 0;
      @*/
    public void delete(Commande commande) {
        String deleteMedicamentsSQL = "DELETE FROM medicament_commande WHERE commande_id = ?";
        String deleteCommandeSQL = "DELETE FROM commande WHERE id = ?";

        try (PreparedStatement ps1 = cnx.prepareStatement(deleteMedicamentsSQL);
             PreparedStatement ps2 = cnx.prepareStatement(deleteCommandeSQL)) {
            ps1.setInt(1, commande.getId());
            ps1.executeUpdate();

            ps2.setInt(1, commande.getId());
            ps2.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException("Échec de la suppression", e);
        }
    }

    /*@ 
      @ requires commande != null;
      @ requires commande.getId() > 0;
      @*/
    @Override
    public void update(Commande commande) {
        String sql = "UPDATE commande SET date_commande = ?, total_prix = ?, quantite = ?, status = ?, stripe_session_id = ? WHERE id = ?";
        try (PreparedStatement pst = cnx.prepareStatement(sql)) {
            pst.setDate(1, Date.valueOf(commande.getDate_commande()));
            pst.setDouble(2, commande.getTotal_prix());
            pst.setInt(3, commande.getQuantite());
            pst.setString(4, commande.getStatus() != null ? commande.getStatus() : "pending");
            pst.setString(5, commande.getStripeSessionId());
            pst.setInt(6, commande.getId());
            pst.executeUpdate();
        } catch (SQLException e) {
            throw new RuntimeException("Échec de la mise à jour", e);
        }
    }

    /*@ 
      @ ensures \result != null;
      @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
      @*/
    @Override
    public List<Commande> readAll() {
        List<Commande> commandes = new ArrayList<>();
        String sql = "SELECT * FROM commande";

        try (Statement st = cnx.createStatement();
             ResultSet rs = st.executeQuery(sql)) {

            while(rs.next()) {
                Commande commande = new Commande(
                        rs.getInt("id"),
                        rs.getDate("date_commande").toLocalDate(),
                        rs.getDouble("total_prix"),
                        rs.getInt("quantite")
                );
                commande.setStatus(rs.getString("status"));
                commande.setStripeSessionId(rs.getString("stripe_session_id"));

                List<MedicamentCommande> medicaments = getMedicamentsForCommande(commande.getId());
                for (MedicamentCommande medicamentCommande : medicaments) {
                    commande.addMedicament(medicamentCommande.getMedicament(), medicamentCommande.getQuantite());
                }

                commandes.add(commande);
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return commandes;
    }

    /*@ 
      @ requires id > 0;
      @ 
      @ ensures \result != null ==> \result.getId() == id;
      @*/
    @Override
    public Commande readById(int id) {
        String sql = "SELECT * FROM commande WHERE id = ?";
        Commande commande = null;

        try (PreparedStatement pst = cnx.prepareStatement(sql)) {
            pst.setInt(1, id);

            try (ResultSet rs = pst.executeQuery()) {
                if(rs.next()) {
                    commande = new Commande(
                            rs.getInt("id"),
                            rs.getDate("date_commande").toLocalDate(),
                            rs.getDouble("total_prix"),
                            rs.getInt("quantite")
                    );
                    commande.setStatus(rs.getString("status"));
                    commande.setStripeSessionId(rs.getString("stripe_session_id"));
                }
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return commande;
    }

    /*@ 
      @ requires commandeId > 0;
      @ ensures \result != null;
      @*/
    public List<MedicamentCommande> getMedicamentsForCommande(int commandeId) {
        List<MedicamentCommande> lignes = new ArrayList<>();
        String sql = "SELECT m.*, cm.quantite FROM medicament_commande cm "
                + "JOIN medicament m ON cm.medicament_id = m.id "
                + "WHERE cm.commande_id = ?";

        try (PreparedStatement pst = cnx.prepareStatement(sql)) {
            pst.setInt(1, commandeId);

            try (ResultSet rs = pst.executeQuery()) {
                while(rs.next()) {
                    Medicament m = new Medicament(
                            rs.getInt("id"),
                            rs.getString("nom_medicament"),
                            rs.getString("description_medicament"),
                            rs.getString("type_medicament"),
                            rs.getDouble("prix_medicament"),
                            rs.getInt("quantite_stock"),
                            rs.getDate("date_entree").toLocalDate(),
                            rs.getDate("date_expiration").toLocalDate()
                    );
                    lignes.add(new MedicamentCommande(null, m, rs.getInt("quantite")));
                }
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return lignes;
    }
}