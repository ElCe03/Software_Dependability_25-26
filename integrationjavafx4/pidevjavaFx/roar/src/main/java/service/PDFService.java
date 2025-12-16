package service;

import com.itextpdf.kernel.pdf.PdfDocument;
import com.itextpdf.kernel.pdf.PdfWriter;
import com.itextpdf.layout.Document;
import com.itextpdf.layout.element.Cell;
import com.itextpdf.layout.element.Paragraph;
import com.itextpdf.layout.element.Table;
import com.itextpdf.layout.properties.TextAlignment;
import com.itextpdf.layout.properties.UnitValue;
import entite.Sejour;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import util.AlertUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class PDFService {
    
    private static final DateTimeFormatter DATE_FORMATTER = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");

    @FunctionalInterface
    public interface FileSelectionStrategy {
        File selectFile(Stage stage, String initialFileName);
    }

    public interface AlertStrategy {
        void showInformation(Stage stage, String title, String content);
        void showError(Stage stage, String title, String content);
    }

    private FileSelectionStrategy fileSelectionStrategy;
    private AlertStrategy alertStrategy;

    public PDFService() {
        this.fileSelectionStrategy = (stage, initialFileName) -> {
            FileChooser fileChooser = new FileChooser();
            fileChooser.setTitle("Enregistrer l'analyse des séjours");
            fileChooser.getExtensionFilters().add(
                    new FileChooser.ExtensionFilter("PDF Files", "*.pdf")
            );
            fileChooser.setInitialFileName(initialFileName);
            return fileChooser.showSaveDialog(stage);
        };

        this.alertStrategy = new AlertStrategy() {
            @Override
            public void showInformation(Stage stage, String title, String content) {
                AlertUtil.showInformation(stage, title, content);
            }

            @Override
            public void showError(Stage stage, String title, String content) {
                AlertUtil.showError(stage, title, content);
            }
        };
    }

    public PDFService(FileSelectionStrategy fileSelectionStrategy, AlertStrategy alertStrategy) {
        this.fileSelectionStrategy = fileSelectionStrategy;
        this.alertStrategy = alertStrategy;
    }
    
    public void generateSejourAnalysisPDF(List<Sejour> sejours, Stage stage) {
        String initialFileName = "analyse_sejours_" + LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyyMMdd_HHmmss")) + ".pdf";
        
        File file = this.fileSelectionStrategy.selectFile(stage, initialFileName);
        
        if (file != null) {
            try {
                PdfWriter writer = new PdfWriter(file);
                PdfDocument pdf = new PdfDocument(writer);
                Document document = new Document(pdf);

                // Add title
                Paragraph title = new Paragraph("Analyse des Séjours");
                title.setTextAlignment(TextAlignment.CENTER);
                title.setFontSize(20);
                title.setBold();
                document.add(title);

                // Add date
                Paragraph date = new Paragraph("Généré le: " + LocalDateTime.now().format(DATE_FORMATTER));
                date.setTextAlignment(TextAlignment.CENTER);
                date.setFontSize(12);
                document.add(date);

                // Add space
                document.add(new Paragraph("\n"));
                
                // Add summary statistics
                addSummaryStatistics(document, sejours);
                
                // Add detailed table
                addDetailedTable(document, sejours);
                
                document.close();
                
                this.alertStrategy.showInformation(stage, "Succès", "Le PDF a été généré avec succès !");
            } catch (FileNotFoundException e) {
                this.alertStrategy.showError(stage, "Erreur", "Erreur lors de la génération du PDF: " + e.getMessage());
            } catch (Exception e) {
                 e.printStackTrace(); 
                this.alertStrategy.showError(stage, "Erreur", "Une erreur inattendue est survenue: " + e.getMessage());
            }
        }
    }
    
    private void addSummaryStatistics(Document document, List<Sejour> sejours) {
        // Calculate statistics
        double totalFrais = 0.0;
        double totalExtras = 0.0;

        for (Sejour s : sejours) {
            totalFrais += s.getFraisSejour();
            totalExtras += s.getPrixExtras();
        }

        double totalRevenue = totalFrais + totalExtras;
        
        // Group by type
        Map<String, Long> countByType = new HashMap<String, Long>();
        for (Sejour s : sejours) {
            String type = s.getTypeSejour() != null ? s.getTypeSejour() : "Non spécifié";
            countByType.put(type, countByType.getOrDefault(type, 0L) + 1L);
        }
        
        // Group by payment status
        Map<String, Long> countByPaymentStatus = new HashMap<String, Long>();
        for (Sejour s : sejours) {
            String status = s.getStatutPaiement() != null ? s.getStatutPaiement() : "Inconnu";
            countByPaymentStatus.put(status, countByPaymentStatus.getOrDefault(status, 0L) + 1L);
        }
        
        // Create summary table
        Table summaryTable = new Table(UnitValue.createPercentArray(2));
        summaryTable.useAllAvailableWidth();

        Cell headerCell = new Cell();
        headerCell.add(new Paragraph("Statistiques Générales"));
        headerCell.setBold();
        summaryTable.addCell(headerCell);
        
        summaryTable.addCell(new Cell().add(new Paragraph("")));
        
        summaryTable.addCell(new Cell().add(new Paragraph("Nombre total de séjours")));
        summaryTable.addCell(new Cell().add(new Paragraph(String.valueOf(sejours.size()))));
        
        summaryTable.addCell(new Cell().add(new Paragraph("Total des frais de séjour")));
        summaryTable.addCell(new Cell().add(new Paragraph(String.format("%.2f €", totalFrais))));
        
        summaryTable.addCell(new Cell().add(new Paragraph("Total des extras")));
        summaryTable.addCell(new Cell().add(new Paragraph(String.format("%.2f €", totalExtras))));
        
        summaryTable.addCell(new Cell().add(new Paragraph("Revenu total")));
        summaryTable.addCell(new Cell().add(new Paragraph(String.format("%.2f €", totalRevenue))));
        
        document.add(summaryTable);
        document.add(new Paragraph("\n"));
        
        // Add type distribution
        Table typeTable = new Table(UnitValue.createPercentArray(2));
        typeTable.useAllAvailableWidth();

        Cell typeHeader = new Cell();
        typeHeader.add(new Paragraph("Distribution par Type"));
        typeHeader.setBold();
        typeTable.addCell(typeHeader);

        typeTable.addCell(new Cell().add(new Paragraph("")));
        
        // Refactoring: Sostituito forEach((k,v) -> ...) con ciclo entrySet
        for (Map.Entry<String, Long> entry : countByType.entrySet()) {
            typeTable.addCell(new Cell().add(new Paragraph(entry.getKey())));
            typeTable.addCell(new Cell().add(new Paragraph(String.valueOf(entry.getValue()))));
        }
        
        document.add(typeTable);
        document.add(new Paragraph("\n"));
        
        // Add payment status distribution
        Table paymentTable = new Table(UnitValue.createPercentArray(2));
        paymentTable.useAllAvailableWidth();

        Cell paymentHeader = new Cell();
        paymentHeader.add(new Paragraph("Distribution par Statut de Paiement"));
        paymentHeader.setBold();
        paymentTable.addCell(paymentHeader);

        paymentTable.addCell(new Cell().add(new Paragraph("")));
        
        for (Map.Entry<String, Long> entry : countByPaymentStatus.entrySet()) {
            paymentTable.addCell(new Cell().add(new Paragraph(entry.getKey())));
            paymentTable.addCell(new Cell().add(new Paragraph(String.valueOf(entry.getValue()))));
        }
        
        document.add(paymentTable);
        document.add(new Paragraph("\n"));
    }
    
    private void addDetailedTable(Document document, List<Sejour> sejours) {
        Table table = new Table(UnitValue.createPercentArray(8));
        table.useAllAvailableWidth();
        
        // Add headers
        String[] headers = {"ID", "Date Entrée", "Date Sortie", "Type", "Frais", "Extras", "Paiement", "Statut"};
        for (String header : headers) {
            Cell c = new Cell();
            c.add(new Paragraph(header));
            c.setBold();
            table.addHeaderCell(c);
        }
        
        // Add data rows
        for (Sejour sejour : sejours) {
            table.addCell(new Cell().add(new Paragraph(String.valueOf(sejour.getId()))));
            
            String dateEntree = sejour.getDateEntree() != null ? sejour.getDateEntree().format(DATE_FORMATTER) : "";
            table.addCell(new Cell().add(new Paragraph(dateEntree)));
            
            String dateSortie = sejour.getDateSortie() != null ? sejour.getDateSortie().format(DATE_FORMATTER) : "";
            table.addCell(new Cell().add(new Paragraph(dateSortie)));
            
            table.addCell(new Cell().add(new Paragraph(sejour.getTypeSejour() != null ? sejour.getTypeSejour() : "")));
            table.addCell(new Cell().add(new Paragraph(String.format("%.2f €", sejour.getFraisSejour()))));
            table.addCell(new Cell().add(new Paragraph(String.format("%.2f €", sejour.getPrixExtras()))));
            table.addCell(new Cell().add(new Paragraph(sejour.getMoyenPaiement() != null ? sejour.getMoyenPaiement() : "")));
            table.addCell(new Cell().add(new Paragraph(sejour.getStatutPaiement() != null ? sejour.getStatutPaiement() : "")));
        }
        
        document.add(table);
    }
}