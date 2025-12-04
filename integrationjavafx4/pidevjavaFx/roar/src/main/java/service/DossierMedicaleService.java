package service;

import entite.DossierMedicale;
import entite.User;
import util.DataSource;

import java.sql.*;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

/**
 * Service class for handling database operations for the DossierMedicale entity
 */
public class DossierMedicaleService {
    private Connection connection;
    private UserServiceE userService;
    private SejourService sejourService;
    
    public DossierMedicaleService() {
        connection = DataSource.getInstance().getConnection();
        userService = new UserServiceE();
    }
    
    public void setSejourService(SejourService sejourService) {
        this.sejourService = sejourService;
    }
    
    /**
     * Add a new medical record to the database
     * @param dossier the medical record to add
     * @return true if successful, false otherwise
     */
    public boolean ajouterDossier(DossierMedicale dossier) {
        String sql = "INSERT INTO dossier_medicale (date_de_creation, historique_des_maladies, " +
                "operations_passees, consultations_passees, statut_dossier, notes, image, " +
                "patient_id, medecin_id) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
            pstmt.setTimestamp(1, Timestamp.valueOf(dossier.getDateDeCreation()));
            pstmt.setString(2, dossier.getHistoriqueDesMaladies());
            pstmt.setString(3, dossier.getOperationsPassees());
            pstmt.setString(4, dossier.getConsultationsPassees());
            pstmt.setString(5, dossier.getStatutDossier());
            pstmt.setString(6, dossier.getNotes());
            pstmt.setString(7, dossier.getImage());
            pstmt.setInt(8, dossier.getPatient().getId());
            pstmt.setInt(9, dossier.getMedecin().getId());
            
            int affectedRows = pstmt.executeUpdate();
            
            if (affectedRows > 0) {
                try (ResultSet generatedKeys = pstmt.getGeneratedKeys()) {
                    if (generatedKeys.next()) {
                        dossier.setId(generatedKeys.getInt(1));
                    }
                }
                return true;
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de l'ajout d'un dossier médical: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Update an existing medical record in the database
     * @param dossier the medical record to update
     * @return true if successful, false otherwise
     */
    public boolean modifierDossier(DossierMedicale dossier) {
        String sql = "UPDATE dossier_medicale SET date_de_creation = ?, historique_des_maladies = ?, " +
                "operations_passees = ?, consultations_passees = ?, statut_dossier = ?, " +
                "notes = ?, image = ?, patient_id = ?, medecin_id = ? WHERE id = ?";
                
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setTimestamp(1, Timestamp.valueOf(dossier.getDateDeCreation()));
            pstmt.setString(2, dossier.getHistoriqueDesMaladies());
            pstmt.setString(3, dossier.getOperationsPassees());
            pstmt.setString(4, dossier.getConsultationsPassees());
            pstmt.setString(5, dossier.getStatutDossier());
            pstmt.setString(6, dossier.getNotes());
            pstmt.setString(7, dossier.getImage());
            pstmt.setInt(8, dossier.getPatient().getId());
            pstmt.setInt(9, dossier.getMedecin().getId());
            pstmt.setInt(10, dossier.getId());
            
            int affectedRows = pstmt.executeUpdate();
            return affectedRows > 0;
        } catch (SQLException e) {
            System.err.println("Erreur lors de la modification d'un dossier médical: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Delete a medical record from the database
     * @param dossierId the ID of the medical record to delete
     * @return true if successful, false otherwise
     */
    public boolean supprimerDossier(int dossierId) {
        String sql = "DELETE FROM dossier_medicale WHERE id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, dossierId);
            
            int affectedRows = pstmt.executeUpdate();
            return affectedRows > 0;
        } catch (SQLException e) {
            System.err.println("Erreur lors de la suppression d'un dossier médical: " + e.getMessage());
            e.printStackTrace();
        }
        
        return false;
    }
    
    /**
     * Get a medical record by its ID, with optional loading of related séjours
     * @param dossierId the ID of the medical record to retrieve
     * @param loadSejours whether to load associated séjours
     * @return the DossierMedicale object if found, null otherwise
     */
    public DossierMedicale recupererDossierParId(int dossierId, boolean loadSejours) {
        String sql = "SELECT * FROM dossier_medicale WHERE id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, dossierId);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                if (rs.next()) {
                    DossierMedicale dossier = extractDossierFromResultSet(rs);
                    
                    // Load associated séjours only if requested and sejourService is initialized
                    if (loadSejours && sejourService != null) {
                        dossier.setSejours(sejourService.recupererSejoursParDossier(dossierId));
                    }
                    
                    return dossier;
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération d'un dossier médical: " + e.getMessage());
            e.printStackTrace();
        }
        
        return null;
    }
    
    /**
     * Get a medical record by its ID, including related séjours
     * @param dossierId the ID of the medical record to retrieve
     * @return the DossierMedicale object if found, null otherwise
     */
    public DossierMedicale recupererDossierParId(int dossierId) {
        return recupererDossierParId(dossierId, true);
    }
    
    /**
     * Get all medical records from the database, with optional loading of related séjours
     * @param loadSejours whether to load associated séjours
     * @return a list of all medical records
     */
    public List<DossierMedicale> recupererTousDossiers(boolean loadSejours) {
        List<DossierMedicale> dossiers = new ArrayList<DossierMedicale>();
        String sql = "SELECT * FROM dossier_medicale";
        
        try (Statement stmt = connection.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            
            while (rs.next()) {
                DossierMedicale dossier = extractDossierFromResultSet(rs);
                dossiers.add(dossier);
            }
            
             // Load associated séjours for each dossier if requested and sejourService is initialized
            if (loadSejours && sejourService != null) {
                for (DossierMedicale dossier : dossiers) {
                    dossier.setSejours(sejourService.recupererSejoursParDossier(dossier.getId()));
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des dossiers médicaux: " + e.getMessage());
            e.printStackTrace();
        }
        
        return dossiers;
    }
    
    /**
     * Get all medical records from the database, including related séjours
     * @return a list of all medical records
     */
    public List<DossierMedicale> recupererTousDossiers() {
        return recupererTousDossiers(true);
    }
    
    /**
     * Get all medical records for a specific patient, with optional loading of related séjours
     * @param patientId the ID of the patient
     * @param loadSejours whether to load associated séjours
     * @return a list of medical records for the patient
     */
    public List<DossierMedicale> recupererDossiersParPatient(int patientId, boolean loadSejours) {
        List<DossierMedicale> dossiers = new ArrayList<DossierMedicale>();
        String sql = "SELECT * FROM dossier_medicale WHERE patient_id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, patientId);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    DossierMedicale dossier = extractDossierFromResultSet(rs);
                    dossiers.add(dossier);
                }
                
                // Load associated séjours for each dossier if requested and sejourService is initialized
                if (loadSejours && sejourService != null) {
                    for (DossierMedicale dossier : dossiers) {
                        dossier.setSejours(sejourService.recupererSejoursParDossier(dossier.getId()));
                    }
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des dossiers médicaux par patient: " + e.getMessage());
            e.printStackTrace();
        }
        
        return dossiers;
    }
    
    /**
     * Get all medical records for a specific patient, including related séjours
     * @param patientId the ID of the patient
     * @return a list of medical records for the patient
     */
    public List<DossierMedicale> recupererDossiersParPatient(int patientId) {
        return recupererDossiersParPatient(patientId, true);
    }
    
    /**
     * Get all medical records for a specific doctor, with optional loading of related séjours
     * @param medecinId the ID of the doctor
     * @param loadSejours whether to load associated séjours
     * @return a list of medical records assigned to the doctor
     */
    public List<DossierMedicale> recupererDossiersParMedecin(int medecinId, boolean loadSejours) {
        List<DossierMedicale> dossiers = new ArrayList<DossierMedicale>();
        String sql = "SELECT * FROM dossier_medicale WHERE medecin_id = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setInt(1, medecinId);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    DossierMedicale dossier = extractDossierFromResultSet(rs);
                    dossiers.add(dossier);
                }
                
                // Load associated séjours for each dossier if requested and sejourService is initialized
                if (loadSejours && sejourService != null) {
                    for (DossierMedicale dossier : dossiers) {
                        dossier.setSejours(sejourService.recupererSejoursParDossier(dossier.getId()));
                    }
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des dossiers médicaux par médecin: " + e.getMessage());
            e.printStackTrace();
        }
        
        return dossiers;
    }
    
    /**
     * Get all medical records for a specific doctor, including related séjours
     * @param medecinId the ID of the doctor
     * @return a list of medical records assigned to the doctor
     */
    public List<DossierMedicale> recupererDossiersParMedecin(int medecinId) {
        return recupererDossiersParMedecin(medecinId, true);
    }
    
    /**
     * Get all medical records with a specific status, with optional loading of related séjours
     * @param statut the status to filter by
     * @param loadSejours whether to load associated séjours
     * @return a list of medical records with the specified status
     */
    public List<DossierMedicale> recupererDossiersParStatut(String statut, boolean loadSejours) {
        List<DossierMedicale> dossiers = new ArrayList<DossierMedicale>();
        String sql = "SELECT * FROM dossier_medicale WHERE statut_dossier = ?";
        
        try (PreparedStatement pstmt = connection.prepareStatement(sql)) {
            pstmt.setString(1, statut);
            
            try (ResultSet rs = pstmt.executeQuery()) {
                while (rs.next()) {
                    DossierMedicale dossier = extractDossierFromResultSet(rs);
                    dossiers.add(dossier);
                }
                
                // Load associated séjours for each dossier if requested and sejourService is initialized
                if (loadSejours && sejourService != null) {
                    for (DossierMedicale dossier : dossiers) {
                        dossier.setSejours(sejourService.recupererSejoursParDossier(dossier.getId()));
                    }
                }
            }
        } catch (SQLException e) {
            System.err.println("Erreur lors de la récupération des dossiers médicaux par statut: " + e.getMessage());
            e.printStackTrace();
        }
        
        return dossiers;
    }
    
    /**
     * Get all medical records with a specific status, including related séjours
     * @param statut the status to filter by
     * @return a list of medical records with the specified status
     */
    public List<DossierMedicale> recupererDossiersParStatut(String statut) {
        return recupererDossiersParStatut(statut, true);
    }
    
    /**
     * Helper method to extract a DossierMedicale object from a ResultSet
     * @param rs the ResultSet containing dossier data
     * @return a DossierMedicale object populated with data from the ResultSet
     * @throws SQLException if there is an error accessing the ResultSet
     */
    private DossierMedicale extractDossierFromResultSet(ResultSet rs) throws SQLException {
        DossierMedicale dossier = new DossierMedicale();
        dossier.setId(rs.getInt("id"));
        
        Timestamp dateCreation = rs.getTimestamp("date_de_creation");
        if (dateCreation != null) {
            dossier.setDateDeCreation(dateCreation.toLocalDateTime());
        } else {
            dossier.setDateDeCreation(LocalDateTime.now());
        }
        
        dossier.setHistoriqueDesMaladies(rs.getString("historique_des_maladies"));
        dossier.setOperationsPassees(rs.getString("operations_passees"));
        dossier.setConsultationsPassees(rs.getString("consultations_passees"));
        dossier.setStatutDossier(rs.getString("statut_dossier"));
        dossier.setNotes(rs.getString("notes"));
        dossier.setImage(rs.getString("image"));
        
        // Load related patient and doctor
        int patientId = rs.getInt("patient_id");
        int medecinId = rs.getInt("medecin_id");
        
        User patient = userService.recupererUserParId(patientId);
        User medecin = userService.recupererUserParId(medecinId);
        
        dossier.setPatient(patient);
        dossier.setMedecin(medecin);
        
        return dossier;
    }
    
    /**
     * Get statistics on medical records
     * @return a map containing various statistics
     */
    public java.util.Map<String, Object> getStatistiques() {
        java.util.Map<String, Object> stats = new java.util.HashMap<String, Object>();
        System.out.println("DossierMedicaleService.getStatistiques() - Starting to fetch statistics");
        
        // Count total dossiers - Make sure we're counting only valid records
        String sqlTotal = "SELECT COUNT(*) FROM dossier_medicale WHERE id IS NOT NULL";
        System.out.println("SQL Query for total dossiers: " + sqlTotal);

        // Count dossiers by status - Use COALESCE to handle NULL values
        String sqlByStatus = "SELECT COALESCE(statut_dossier, 'Non défini') as statut, COUNT(*) as count " +
                            "FROM dossier_medicale " +
                            "GROUP BY COALESCE(statut_dossier, 'Non défini')";
        System.out.println("SQL Query for dossiers by status: " + sqlByStatus);

                            // Count dossiers created per month in current year - Handle NULL dates
        String sqlByMonth = "SELECT MONTH(COALESCE(date_de_creation, CURRENT_DATE())) as month, COUNT(*) as count " +
                         "FROM dossier_medicale " +
                         "WHERE YEAR(COALESCE(date_de_creation, CURRENT_DATE())) = YEAR(CURRENT_DATE()) " +
                         "GROUP BY MONTH(COALESCE(date_de_creation, CURRENT_DATE())) " +
                         "ORDER BY month";
        System.out.println("SQL Query for dossiers by month: " + sqlByMonth);
        
        // Get count of dossiers per medecin - Include INNER JOIN to ensure only valid medecins
        String sqlByMedecin = "SELECT m.id, m.nom, m.prenom, COUNT(d.id) as count " +
                           "FROM dossier_medicale d " +
                           "INNER JOIN user m ON d.medecin_id = m.id " +
                           "WHERE m.id IS NOT NULL " +
                           "GROUP BY m.id, m.nom, m.prenom " +
                           "ORDER BY count DESC";
        System.out.println("SQL Query for dossiers by medecin: " + sqlByMedecin);

        try (Statement stmt = connection.createStatement()) {
            // Get total count
            try (ResultSet rs = stmt.executeQuery(sqlTotal)) {
                if (rs.next()) {
                    int total = rs.getInt(1);
                    stats.put("totalDossiers", total);
                    System.out.println("Found " + total + " total dossiers");
                }
            } catch (SQLException e) {
                System.err.println("Error executing total dossiers query: " + e.getMessage());
                e.printStackTrace();
            }
            
            // Get counts by status
            java.util.Map<String, Integer> statsByStatus = new java.util.HashMap<String, Integer>();
            try (ResultSet rs = stmt.executeQuery(sqlByStatus)) {
                while (rs.next()) {
                    String status = rs.getString("statut");
                    int count = rs.getInt("count");
                    statsByStatus.put(status, count);
                    System.out.println("Found " + count + " dossiers with status: " + status);
                }
            } catch (SQLException e) {
                System.err.println("Error executing dossiers by status query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("dossiersByStatus", (Object) statsByStatus);
            
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
                    System.out.println("Found " + count + " dossiers for month: " + month);
                }
            } catch (SQLException e) {
                System.err.println("Error executing dossiers by month query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("dossiersByMonth", (Object) statsByMonth);
            
            // Get count by medecin
            List<java.util.Map<String, Object>> statsByMedecin = new ArrayList<java.util.Map<String, Object>>();
            try (ResultSet rs = stmt.executeQuery(sqlByMedecin)) {
                while (rs.next()) {
                    java.util.Map<String, Object> medecinStat = new java.util.HashMap<String, Object>();
                    int id = rs.getInt("id");
                    String nom = rs.getString("nom");
                    String prenom = rs.getString("prenom");
                    int count = rs.getInt("count");
                    
                    medecinStat.put("id", id);
                    medecinStat.put("nom", nom);
                    medecinStat.put("prenom", prenom);
                    medecinStat.put("count", count);
                    statsByMedecin.add(medecinStat);
                    
                    System.out.println("Found " + count + " dossiers for medecin: " + prenom + " " + nom);
                }
            } catch (SQLException e) {
                System.err.println("Error executing dossiers by medecin query: " + e.getMessage());
                e.printStackTrace();
            }
            stats.put("dossiersByMedecin", (Object) statsByMedecin);
            
            System.out.println("DossierMedicaleService.getStatistiques() completed successfully");
        } catch (SQLException e) {
            System.err.println("Error in DossierMedicaleService.getStatistiques(): " + e.getMessage());
            e.printStackTrace();
        }
        
        return stats;
    }    
}