package service;

import entite.DossierMedicale;
import entite.Sejour;
import util.DataSource;

import java.sql.*;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

/**
 * Service class for handling database operations for the Sejour entity
 */
public class SejourService {
    private Connection connection;
    private DossierMedicaleService dossierService;
    
    public SejourService() {
        this(DataSource.getInstance().getConnection());
    }

    public SejourService(Connection connection) {
        this.connection = connection;
    }
    
    public void setDossierService(DossierMedicaleService dossierService) {
        this.dossierService = dossierService;
    }
    
    /**
     * Add a new stay to the database
     * @param sejour the stay to add
     * @return true if successful, false otherwise
     */
    public boolean ajouterSejour(Sejour sejour) {
        // Validate that exit date is after entry date
        if (sejour.getDateSortie() != null && sejour.getDateEntree() != null &&
                sejour.getDateSortie().isBefore(sejour.getDateEntree())) {
            System.err.println("Erreur: La date de sortie doit être après la date d'entrée");
            return false;
        }
        
        // Validate that costs are positive
        if (sejour.getFraisSejour() < 0 || sejour.getPrixExtras() < 0) {
            System.err.println("Erreur: Les frais doivent être positifs");
            return false;
        }
        
        // Validate that dossierMedicale is not null
        if (sejour.getDossierMedicale() == null) {
            System.err.println("Erreur: Un dossier médical doit être associé au séjour");
            return false;
        }
        
        // Match exactly the columns in the database
        String sql = "INSERT INTO sejour (dossier_medicale_id, date_entree, date_sortie, type_sejour, " +
                "frais_sejour, moyen_paiement, statut_paiement, prix_extras) " +
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?)";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
            // Ensure dateEntree is not null
            if (sejour.getDateEntree() == null) {
                sejour.setDateEntree(LocalDateTime.now());
            }
            
            // Ensure date_sortie is not null (as required by the database)
            if (sejour.getDateSortie() == null) {
                // Set a default date_sortie to the same as date_entree plus 1 day
                sejour.setDateSortie(sejour.getDateEntree().plusDays(1));
            }
            
            // Set parameters in the same order as in the SQL statement
            pstmt.setInt(1, sejour.getDossierMedicale().getId());
            pstmt.setTimestamp(2, Timestamp.valueOf(sejour.getDateEntree()));
            pstmt.setTimestamp(3, Timestamp.valueOf(sejour.getDateSortie()));
            
            String typeSejour = sejour.getTypeSejour();
            if (typeSejour == null) typeSejour = "";
            pstmt.setString(4, typeSejour);
            
            pstmt.setDouble(5, sejour.getFraisSejour());
            
            // Ensure moyen_paiement is not null (as required by the database)
            String moyenPaiement = sejour.getMoyenPaiement();
            if (moyenPaiement == null) moyenPaiement = "Non spécifié";
            pstmt.setString(6, moyenPaiement);
            
            // Ensure statut_paiement is not null (as required by the database)
            String statutPaiement = sejour.getStatutPaiement();
            if (statutPaiement == null) statutPaiement = "En attente";
            pstmt.setString(7, statutPaiement);
            
            // prix_extras can be null in the database
            if (sejour.getPrixExtras() > 0) {
                pstmt.setDouble(8, sejour.getPrixExtras());
            } else {
                pstmt.setNull(8, Types.DOUBLE);
            }
            
            System.out.println("Executing SQL: " + sql);
            
            int affectedRows = pstmt.executeUpdate();
            
            if (affectedRows > 0) {
                try (ResultSet generatedKeys = pstmt.getGeneratedKeys()) {
                    if (generatedKeys.next()) {
                        sejour.setId(generatedKeys.getInt(1));
                        return true;
                    }
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de l'ajout d'un séjour: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Update an existing stay in the database
     * @param sejour the stay to update
     * @return true if successful, false otherwise
     */
    public boolean modifierSejour(Sejour sejour) {
        // Validate that exit date is after entry date
        if (sejour.getDateSortie() != null && sejour.getDateEntree() != null &&
                sejour.getDateSortie().isBefore(sejour.getDateEntree())) {
            System.err.println("Erreur: La date de sortie doit être après la date d'entrée");
            return false;
        }
        
        // Validate that costs are positive
        if (sejour.getFraisSejour() < 0 || sejour.getPrixExtras() < 0) {
            System.err.println("Erreur: Les frais doivent être positifs");
            return false;
        }
        
        // Validate that dossierMedicale is not null
        if (sejour.getDossierMedicale() == null) {
            System.err.println("Erreur: Un dossier médical doit être associé au séjour");
            return false;
        }
        
        // Ensure date_sortie is not null (as required by the database)
        if (sejour.getDateSortie() == null) {
            // Set a default date_sortie to the same as date_entree plus 1 day
            sejour.setDateSortie(sejour.getDateEntree().plusDays(1));
        }
        
        // Match exactly the columns in the database
        String sql = "UPDATE sejour SET dossier_medicale_id = ?, date_entree = ?, date_sortie = ?, " +
                "type_sejour = ?, frais_sejour = ?, moyen_paiement = ?, statut_paiement = ?, " +
                "prix_extras = ? WHERE id = ?";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, sejour.getDossierMedicale().getId());
            pstmt.setTimestamp(2, Timestamp.valueOf(sejour.getDateEntree()));
            pstmt.setTimestamp(3, Timestamp.valueOf(sejour.getDateSortie()));
            
            String typeSejour = sejour.getTypeSejour();
            if (typeSejour == null) typeSejour = "";
            pstmt.setString(4, typeSejour);
            
            pstmt.setDouble(5, sejour.getFraisSejour());
            
             // Ensure moyen_paiement is not null (as required by the database)
            String moyenPaiement = sejour.getMoyenPaiement();
            if (moyenPaiement == null) moyenPaiement = "Non spécifié";
            pstmt.setString(6, moyenPaiement);
            
            // Ensure statut_paiement is not null (as required by the database)
            String statutPaiement = sejour.getStatutPaiement();
            if (statutPaiement == null) statutPaiement = "En attente";
            pstmt.setString(7, statutPaiement);
            
            // prix_extras can be null in the database
            if (sejour.getPrixExtras() > 0) {
                pstmt.setDouble(8, sejour.getPrixExtras());
            } else {
                pstmt.setNull(8, Types.DOUBLE);
            }
            
            pstmt.setInt(9, sejour.getId());
            
            System.out.println("Executing SQL update: " + sql);
            
            int affectedRows = pstmt.executeUpdate();
            return affectedRows > 0;
        } catch (SQLException e) {
            System.err.println("Erreur lors de la modification d'un séjour: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Delete a stay from the database
     * @param sejourId the ID of the stay to delete
     * @return true if successful, false otherwise
     */
    public boolean supprimerSejour(int sejourId) {
        String sql = "DELETE FROM sejour WHERE id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, sejourId);
            
            int affectedRows = pstmt.executeUpdate();
            return affectedRows > 0;
        } catch (SQLException e) {
            System.err.println("Erreur lors de la suppression d'un séjour: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Get a stay by its ID
     * @param sejourId the ID of the stay to retrieve
     * @return the Sejour object if found, null otherwise
     */
    public Sejour recupererSejourParId(int sejourId) {
        String sql = "SELECT * FROM sejour WHERE id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, sejourId);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                if (rs.next()) {
                    return extractSejourFromResultSet(rs);
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération d'un séjour: " + e.getMessage());
            e.printStackTrace();
        }
        
        return null;
    }
    
    /**
     * Get all stays from the database
     * @return a list of all stays
     */
    public List<Sejour> recupererTousSejours() {
        List<Sejour> sejours = new ArrayList<Sejour>();
        String sql = "SELECT * FROM sejour";
        
        try (Statement stmt = connection.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            
            while (rs.next()) {
                Sejour sejour = extractSejourFromResultSet(rs);
                sejours.add(sejour);
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des séjours: " + e.getMessage());
            e.printStackTrace();
        }
        
        return sejours;
    }
    
    /**
     * Get all stays for a specific medical record
     * @param dossierId the ID of the medical record
     * @return a list of stays for the given medical record
     */
    public List<Sejour> recupererSejoursParDossier(int dossierId) {
        List<Sejour> sejours = new ArrayList<Sejour>();
        String sql = "SELECT * FROM sejour WHERE dossier_medicale_id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, dossierId);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    Sejour sejour = extractSejourFromResultSet(rs);
                    sejours.add(sejour);
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des séjours par dossier: " + e.getMessage());
            e.printStackTrace();
        }
        
        return sejours;
    }
    
    /**
     * Get all stays with a specific payment status
     * @param statutPaiement the payment status to filter by
     * @return a list of stays with the specified payment status
     */
    public List<Sejour> recupererSejoursParStatutPaiement(String statutPaiement) {
        List<Sejour> sejours = new ArrayList<Sejour>();
        String sql = "SELECT * FROM sejour WHERE statut_paiement = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setString(1, statutPaiement);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    Sejour sejour = extractSejourFromResultSet(rs);
                    sejours.add(sejour);
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des séjours par statut de paiement: " + e.getMessage());
            e.printStackTrace();
        }
        
        return sejours;
    }
    
    /**
     * Helper method to extract a Sejour object from a ResultSet
     * @param rs the ResultSet containing stay data
     * @return a Sejour object populated with data from the ResultSet
     * @throws SQLException if there is an error accessing the ResultSet
     */
    private Sejour extractSejourFromResultSet(ResultSet rs) throws SQLException {
        Sejour sejour = new Sejour();
        sejour.setId(rs.getInt("id"));
        
        Timestamp dateEntree = rs.getTimestamp("date_entree");
        if (dateEntree != null) {
            sejour.setDateEntree(dateEntree.toLocalDateTime());
        } else {
            sejour.setDateEntree(LocalDateTime.now());
        }
        
        Timestamp dateSortie = rs.getTimestamp("date_sortie");
        if (dateSortie != null) {
            sejour.setDateSortie(dateSortie.toLocalDateTime());
        }
        
        sejour.setTypeSejour(rs.getString("type_sejour"));
        sejour.setFraisSejour(rs.getDouble("frais_sejour"));
        
        String moyenPaiement = rs.getString("moyen_paiement");
        sejour.setMoyenPaiement(moyenPaiement);
        
        String statutPaiement = rs.getString("statut_paiement");
        if (statutPaiement == null) statutPaiement = "En attente";
        sejour.setStatutPaiement(statutPaiement);
        
        double prixExtras = rs.getDouble("prix_extras");
        if (!rs.wasNull()) {
            sejour.setPrixExtras(prixExtras);
        }
        
        int dossierMedicaleId = rs.getInt("dossier_medicale_id");
        
        // Only set the ID of the dossier without loading the entire object to prevent circular references
        if (dossierMedicaleId > 0) {
            DossierMedicale dossier = new DossierMedicale();
            dossier.setId(dossierMedicaleId);
            sejour.setDossierMedicale(dossier);
        }
        
        return sejour;
    }
    
    /**
     * Get statistics on patient stays
     * @return a map containing various statistics
     */
    public java.util.Map<String, Object> getStatistiques() {
        java.util.Map<String, Object> stats = new java.util.HashMap<String, Object>();
        System.out.println("SejourService.getStatistiques() - Starting to fetch statistics");
        
        // Count total sejours - make sure we count only valid records
        String sqlTotal = "SELECT COUNT(*) FROM sejour WHERE id IS NOT NULL";
        System.out.println("SQL Query for total sejours: " + sqlTotal);
        
        // Count sejours by type - handle NULL values
        String sqlByType = "SELECT COALESCE(type_sejour, 'Non défini') as type, COUNT(*) as count " +
                         "FROM sejour " +
                         "GROUP BY COALESCE(type_sejour, 'Non défini')";
        System.out.println("SQL Query for sejours by type: " + sqlByType);
                          
        // Count sejours by payment status - handle NULL values
        String sqlByPaymentStatus = "SELECT COALESCE(statut_paiement, 'En attente') as status, COUNT(*) as count " +
                                "FROM sejour " +
                                "GROUP BY COALESCE(statut_paiement, 'En attente')";
        System.out.println("SQL Query for sejours by payment status: " + sqlByPaymentStatus);
        
        // Count sejours started per month in current year - handle NULL dates
        String sqlByMonth = "SELECT MONTH(COALESCE(date_entree, CURRENT_DATE())) as month, COUNT(*) as count " +
                         "FROM sejour " +
                         "WHERE YEAR(COALESCE(date_entree, CURRENT_DATE())) = YEAR(CURRENT_DATE()) " +
                         "GROUP BY MONTH(COALESCE(date_entree, CURRENT_DATE())) " +
                         "ORDER BY month";
        System.out.println("SQL Query for sejours by month: " + sqlByMonth);
        
        // Calculate average stay duration in days - handle NULL dates
        String sqlAvgDuration = "SELECT AVG(CASE WHEN date_sortie IS NOT NULL THEN " +
                            "DATEDIFF(date_sortie, date_entree) " +
                            "ELSE DATEDIFF(CURRENT_DATE(), date_entree) END) as avg_duration " +
                            "FROM sejour " +
                            "WHERE date_entree IS NOT NULL";
        System.out.println("SQL Query for average duration: " + sqlAvgDuration);
        
        // Calculate total revenue - handle NULL values
        String sqlTotalRevenue = "SELECT SUM(COALESCE(frais_sejour, 0) + COALESCE(prix_extras, 0)) as total_revenue FROM sejour";
        System.out.println("SQL Query for total revenue: " + sqlTotalRevenue);
        
        // Calculate revenue by month - handle NULL values
        String sqlRevenueByMonth = "SELECT MONTH(COALESCE(date_entree, CURRENT_DATE())) as month, " +
                                "SUM(COALESCE(frais_sejour, 0) + COALESCE(prix_extras, 0)) as revenue " +
                                "FROM sejour " +
                                "WHERE YEAR(COALESCE(date_entree, CURRENT_DATE())) = YEAR(CURRENT_DATE()) " +
                                "GROUP BY MONTH(COALESCE(date_entree, CURRENT_DATE())) " +
                                "ORDER BY month";
        System.out.println("SQL Query for revenue by month: " + sqlRevenueByMonth);
                              
        try (Statement stmt = connection.createStatement()) {
            // Get total count
            try (ResultSet rs = stmt.executeQuery(sqlTotal)) {
                if (rs.next()) {
                    int total = rs.getInt(1);
                    stats.put("totalSejours", total);
                    System.out.println("Found " + total + " total sejours");
                }
            } catch (SQLException e) {
                System.err.println("Error executing total sejours query: " + e.getMessage());
                e.printStackTrace();
            }
            
            // Get counts by type
            java.util.Map<String, Integer> statsByType = new java.util.HashMap<String, Integer>();
            try (ResultSet rs = stmt.executeQuery(sqlByType)) {
                while (rs.next()) {
                    String type = rs.getString("type");
                    int count = rs.getInt("count");
                    statsByType.put(type, count);
                    System.out.println("Found " + count + " sejours with type: " + type);
                }
            } catch (SQLException e) {
                System.err.println("Error executing sejours by type query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("sejoursByType", (Object) statsByType);
            
            // Get counts by payment status
            java.util.Map<String, Integer> statsByPaymentStatus = new java.util.HashMap<String, Integer>();
            try (ResultSet rs = stmt.executeQuery(sqlByPaymentStatus)) {
                while (rs.next()) {
                    String status = rs.getString("status");
                    int count = rs.getInt("count");
                    statsByPaymentStatus.put(status, count);
                    System.out.println("Found " + count + " sejours with payment status: " + status);
                }
            } catch (SQLException e) {
                System.err.println("Error executing sejours by payment status query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("sejoursByPaymentStatus", (Object) statsByPaymentStatus);
            
            // Get counts by month
            java.util.Map<Integer, Integer> statsByMonth = new java.util.HashMap<Integer, Integer>();
            for (int i = 1; i <= 12; i++) {
                statsByMonth.put(i, 0); // Initialize all months with 0
            }
            try (ResultSet rs = stmt.executeQuery(sqlByMonth)) {
                while (rs.next()) {
                    int month = rs.getInt("month");
                    int count = rs.getInt("count");
                    statsByMonth.put(month, count);
                    System.out.println("Found " + count + " sejours for month: " + month);
                }
            } catch (SQLException e) {
                System.err.println("Error executing sejours by month query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("sejoursByMonth", (Object) statsByMonth);
            
            // Get average duration
            try (ResultSet rs = stmt.executeQuery(sqlAvgDuration)) {
                if (rs.next()) {
                    Object avgDurationObj = rs.getObject("avg_duration");
                    double avgDurationValue;
                    if (avgDurationObj != null) {
                        avgDurationValue = rs.getDouble("avg_duration");
                    } else {
                        avgDurationValue = 0.0;
                    }
                    stats.put("averageDuration", avgDurationValue);
                    System.out.println("Average sejour duration: " + avgDurationValue + " days");
                }
            } catch (SQLException e) {
                System.err.println("Error executing average duration query: " + e.getMessage());
                e.printStackTrace();
            }
            
            // Get total revenue
            try (ResultSet rs = stmt.executeQuery(sqlTotalRevenue)) {
                if (rs.next()) {
                    Object totalRevenueObj = rs.getObject("total_revenue");
                    double totalRevenueValue;
                    if (totalRevenueObj != null) {
                        totalRevenueValue = rs.getDouble("total_revenue");
                    } else {
                        totalRevenueValue = 0.0;
                    }
                    stats.put("totalRevenue", totalRevenueValue);
                    System.out.println("Total revenue: " + totalRevenueValue);
                }
            } catch (SQLException e) {
                System.err.println("Error executing total revenue query: " + e.getMessage());
                e.printStackTrace();
            }
            
            // Get revenue by month
            java.util.Map<Integer, Double> revenueByMonth = new java.util.HashMap<Integer, Double>();
            for (int i = 1; i <= 12; i++) {
                revenueByMonth.put(i, 0.0); // Initialize all months with 0
            }
            try (ResultSet rs = stmt.executeQuery(sqlRevenueByMonth)) {
                while (rs.next()) {
                    int month = rs.getInt("month");
                    double revenue = rs.getDouble("revenue");
                    revenueByMonth.put(month, revenue);
                    System.out.println("Revenue for month " + month + ": " + revenue);
                }
            } catch (SQLException e) {
                System.err.println("Error executing revenue by month query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("revenueByMonth", (Object) revenueByMonth);
            
            System.out.println("SejourService.getStatistiques() completed successfully");
            
        } catch (SQLException e) {
            System.err.println("Error in SejourService.getStatistiques(): " + e.getMessage());
            e.printStackTrace();
        }
        
        return stats;
    }

    public List<Sejour> getAllSejours() {
        List<Sejour> sejours = new ArrayList<Sejour>();
        String query = "SELECT * FROM sejour";
        
        try (PreparedStatement stmt = connection.prepareStatement(query);
             ResultSet rs = stmt.executeQuery()) {
            
            while (rs.next()) {
                Sejour sejour = new Sejour();
                sejour.setId(rs.getInt("id"));
                sejour.setDateEntree(rs.getTimestamp("date_entree").toLocalDateTime());
                
                Timestamp tsSortie = rs.getTimestamp("date_sortie");
                if (tsSortie != null) {
                    sejour.setDateSortie(tsSortie.toLocalDateTime());
                } else {
                    sejour.setDateSortie(null);
                }

                sejour.setTypeSejour(rs.getString("type_sejour"));
                sejour.setFraisSejour(rs.getDouble("frais_sejour"));
                sejour.setPrixExtras(rs.getDouble("prix_extras"));
                sejour.setMoyenPaiement(rs.getString("moyen_paiement"));
                sejour.setStatutPaiement(rs.getString("statut_paiement"));
                sejours.add(sejour);
            }
        } catch (SQLException e) {
            System.err.println("Error retrieving all stays: " + e.getMessage());
            e.printStackTrace();
        }
        
        return sejours;
    }
}