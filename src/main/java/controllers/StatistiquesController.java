package controllers;

import entite.Sejour;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.chart.BarChart;
import javafx.scene.chart.LineChart;
import javafx.scene.chart.PieChart;
import javafx.scene.chart.XYChart;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.GridPane;
import javafx.stage.Stage;
import service.DossierMedicaleService;
import service.PDFService;
import service.SejourService;
import util.AlertUtil;

import java.net.URL;
import java.text.NumberFormat;
import java.time.Month;
import java.util.*;

/**
 * Controller for the statistics view in the backoffice
 */
public class StatistiquesController implements Initializable {

    @FXML private Label lblTotalDossiers;
    @FXML private Label lblTotalSejours;
    @FXML private Label lblAverageDuration;
    @FXML private Label lblTotalRevenue;
    
    @FXML private PieChart chartDossierStatus;
    @FXML private PieChart chartSejourTypes;
    @FXML private PieChart chartPaymentStatus;
    
    @FXML private BarChart<String, Number> chartDossiersByMonth;
    @FXML private BarChart<String, Number> chartSejoursByMonth;
    
    @FXML private LineChart<String, Number> chartRevenueByMonth;
    
    @FXML private GridPane gridMedecinStats;
    
    @FXML private Button btnExportPDF;
    
    private DossierMedicaleService dossierService;
    private SejourService sejourService;
    private PDFService pdfService;
    
    private final NumberFormat currencyFormat = NumberFormat.getCurrencyInstance(Locale.FRANCE);
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        dossierService = new DossierMedicaleService();
        sejourService = new SejourService();
        pdfService = new PDFService();
        

        dossierService.setSejourService(sejourService);
        sejourService.setDossierService(dossierService);
        
        loadStatistics();
    }
    
    /**
     * Load all statistics data and populate the charts and labels
     */
    private void loadStatistics() {
        try {
            System.out.println("Starting to load statistics data...");
            

            Map<String, Object> dossierStats = dossierService.getStatistiques();
            System.out.println("Dossier Stats: " + (dossierStats != null ? dossierStats.toString() : "null"));
            
            Map<String, Object> sejourStats = sejourService.getStatistiques();
            System.out.println("Sejour Stats: " + (sejourStats != null ? sejourStats.toString() : "null"));
            
            if (dossierStats == null) {
                dossierStats = new HashMap<>();
                System.err.println("Warning: dossierStats is null");
            }
            
            if (sejourStats == null) {
                sejourStats = new HashMap<>();
                System.err.println("Warning: sejourStats is null");
            }
            

            System.out.println("totalDossiers: " + dossierStats.get("totalDossiers"));
            System.out.println("dossiersByStatus: " + dossierStats.get("dossiersByStatus"));
            System.out.println("dossiersByMonth: " + dossierStats.get("dossiersByMonth"));
            System.out.println("dossiersByMedecin: " + dossierStats.get("dossiersByMedecin"));
            
            System.out.println("totalSejours: " + sejourStats.get("totalSejours"));
            System.out.println("sejoursByType: " + sejourStats.get("sejoursByType"));
            System.out.println("sejoursByPaymentStatus: " + sejourStats.get("sejoursByPaymentStatus"));
            System.out.println("sejoursByMonth: " + sejourStats.get("sejoursByMonth"));
            System.out.println("averageDuration: " + sejourStats.get("averageDuration"));
            System.out.println("totalRevenue: " + sejourStats.get("totalRevenue"));
            System.out.println("revenueByMonth: " + sejourStats.get("revenueByMonth"));
            

            Integer totalDossiers = (Integer) dossierStats.getOrDefault("totalDossiers", 0);
            lblTotalDossiers.setText(String.valueOf(totalDossiers));
            
            Integer totalSejours = (Integer) sejourStats.getOrDefault("totalSejours", 0);
            lblTotalSejours.setText(String.valueOf(totalSejours));
            

            Object avgDurationObj = sejourStats.getOrDefault("averageDuration", 0.0);
            double avgDuration = 0.0;
            if (avgDurationObj instanceof Number) {
                avgDuration = ((Number) avgDurationObj).doubleValue();
            }
            lblAverageDuration.setText(String.format("%.1f jours", avgDuration));
            

            Object totalRevenueObj = sejourStats.getOrDefault("totalRevenue", 0.0);
            double totalRevenue = 0.0;
            if (totalRevenueObj instanceof Number) {
                totalRevenue = ((Number) totalRevenueObj).doubleValue();
            }
            lblTotalRevenue.setText(currencyFormat.format(totalRevenue));
            

            Map<String, Integer> dossiersByStatus = (Map<String, Integer>) dossierStats.getOrDefault("dossiersByStatus", new HashMap<String, Integer>());
            populateDossierStatusChart(dossiersByStatus);
            

            Map<String, Integer> sejoursByType = (Map<String, Integer>) sejourStats.getOrDefault("sejoursByType", new HashMap<String, Integer>());
            populateSejourTypeChart(sejoursByType);
            

            Map<String, Integer> sejoursByPaymentStatus = (Map<String, Integer>) sejourStats.getOrDefault("sejoursByPaymentStatus", new HashMap<String, Integer>());
            populatePaymentStatusChart(sejoursByPaymentStatus);
            

            Map<Integer, Integer> dossiersByMonth = (Map<Integer, Integer>) dossierStats.getOrDefault("dossiersByMonth", new HashMap<Integer, Integer>());
            populateDossiersByMonthChart(dossiersByMonth);
            

            Map<Integer, Integer> sejoursByMonth = (Map<Integer, Integer>) sejourStats.getOrDefault("sejoursByMonth", new HashMap<Integer, Integer>());
            populateSejoursByMonthChart(sejoursByMonth);
            

            Map<Integer, Double> revenueByMonth = (Map<Integer, Double>) sejourStats.getOrDefault("revenueByMonth", new HashMap<Integer, Double>());
            populateRevenueByMonthChart(revenueByMonth);
            

            List<Map<String, Object>> dossiersByMedecin = (List<Map<String, Object>>) dossierStats.getOrDefault("dossiersByMedecin", new ArrayList<Map<String, Object>>());
            populateMedecinStats(dossiersByMedecin);
            
            System.out.println("Statistics loaded successfully.");
        } catch (Exception e) {
            System.err.println("Error loading statistics: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the dossier status pie chart
     */
    private void populateDossierStatusChart(Map<String, Integer> data) {
        try {
            chartDossierStatus.getData().clear();
            
            if (data != null) {
                data.forEach((status, count) -> {
                    if (status != null && !status.isEmpty() && count != null) {
                        chartDossierStatus.getData().add(new PieChart.Data(status, count));
                    }
                });
            }
        } catch (Exception e) {
            System.err.println("Error populating dossier status chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the sejour type pie chart
     */
    private void populateSejourTypeChart(Map<String, Integer> data) {
        try {
            chartSejourTypes.getData().clear();
            
            if (data != null) {
                data.forEach((type, count) -> {
                    if (type != null && !type.isEmpty() && count != null) {
                        chartSejourTypes.getData().add(new PieChart.Data(type, count));
                    }
                });
            }
        } catch (Exception e) {
            System.err.println("Error populating sejour type chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the payment status pie chart
     */
    private void populatePaymentStatusChart(Map<String, Integer> data) {
        try {
            chartPaymentStatus.getData().clear();
            
            if (data != null) {
                data.forEach((status, count) -> {
                    if (status != null && !status.isEmpty() && count != null) {
                        chartPaymentStatus.getData().add(new PieChart.Data(status, count));
                    }
                });
            }
        } catch (Exception e) {
            System.err.println("Error populating payment status chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the dossiers by month bar chart
     */
    private void populateDossiersByMonthChart(Map<Integer, Integer> data) {
        try {
            chartDossiersByMonth.getData().clear();
            
            if (data != null) {
                XYChart.Series<String, Number> series = new XYChart.Series<>();
                series.setName("Dossiers Créés");
                
                for (int i = 1; i <= 12; i++) {
                    String monthName = Month.of(i).toString().substring(0, 3);
                    Integer value = data.getOrDefault(i, 0);
                    series.getData().add(new XYChart.Data<>(monthName, value));
                }
                
                chartDossiersByMonth.getData().add(series);
            }
        } catch (Exception e) {
            System.err.println("Error populating dossiers by month chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the sejours by month bar chart
     */
    private void populateSejoursByMonthChart(Map<Integer, Integer> data) {
        try {
            chartSejoursByMonth.getData().clear();
            
            if (data != null) {
                XYChart.Series<String, Number> series = new XYChart.Series<>();
                series.setName("Séjours Commencés");
                
                for (int i = 1; i <= 12; i++) {
                    String monthName = Month.of(i).toString().substring(0, 3);
                    Integer value = data.getOrDefault(i, 0);
                    series.getData().add(new XYChart.Data<>(monthName, value));
                }
                
                chartSejoursByMonth.getData().add(series);
            }
        } catch (Exception e) {
            System.err.println("Error populating sejours by month chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the revenue by month line chart
     */
    private void populateRevenueByMonthChart(Map<Integer, Double> data) {
        try {
            chartRevenueByMonth.getData().clear();

            if (data != null) {
                XYChart.Series<String, Number> series = new XYChart.Series<>();
                series.setName("Revenus");
                
                for (int i = 1; i <= 12; i++) {
                    String monthName = Month.of(i).toString().substring(0, 3);
                    Double value = data.getOrDefault(i, 0.0);
                    series.getData().add(new XYChart.Data<>(monthName, value));
                }
                
                chartRevenueByMonth.getData().add(series);
            }
        } catch (Exception e) {
            System.err.println("Error populating revenue by month chart: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Populate the medecin statistics grid
     */
    private void populateMedecinStats(List<Map<String, Object>> data) {
        try {
            gridMedecinStats.getChildren().clear();
            

            Label lblHeader1 = new Label("Médecin");
            Label lblHeader2 = new Label("Dossiers");
            gridMedecinStats.add(lblHeader1, 0, 0);
            gridMedecinStats.add(lblHeader2, 1, 0);
            

            lblHeader1.getStyleClass().add("stat-header");
            lblHeader2.getStyleClass().add("stat-header");
            
            if (data != null) {
                int row = 1;
                for (Map<String, Object> medecinStat : data) {
                    if (medecinStat == null) continue;
                    
                    String nom = (String) medecinStat.getOrDefault("nom", "");
                    String prenom = (String) medecinStat.getOrDefault("prenom", "");
                    
                    Object countObj = medecinStat.get("count");
                    int count = 0;
                    if (countObj instanceof Number) {
                        count = ((Number) countObj).intValue();
                    }
                    
                    Label lblMedecin = new Label((prenom != null ? prenom : "") + " " + (nom != null ? nom : ""));
                    Label lblCount = new Label(String.valueOf(count));
                    
                    gridMedecinStats.add(lblMedecin, 0, row);
                    gridMedecinStats.add(lblCount, 1, row);
                    
                    row++;
                    
                    // Limit to top 10 medecins
                    if (row > 10) {
                        break;
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("Error populating medecin stats: " + e.getMessage());
            e.printStackTrace();
        }
    }

    @FXML
    private void handleExportPDF(ActionEvent event) {
        Stage stage = null;
        try {

            List<Sejour> sejours = sejourService.getAllSejours();
            

            stage = (Stage) btnExportPDF.getScene().getWindow();
            

            pdfService.generateSejourAnalysisPDF(sejours, stage);
        } catch (Exception e) {

            if (stage == null && event.getSource() instanceof Node) {
                stage = (Stage) ((Node) event.getSource()).getScene().getWindow();
            }
            

            if (stage == null) {
                stage = (Stage) btnExportPDF.getScene().getWindow();
            }
            
            AlertUtil.showError(stage, "Erreur", "Une erreur est survenue lors de l'exportation du PDF: " + e.getMessage());
        }
    }
} 