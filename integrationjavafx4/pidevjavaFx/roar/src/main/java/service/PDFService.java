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
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class PDFService {
    
    private static final DateTimeFormatter DATE_FORMATTER = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm");
    
    public void generateSejourAnalysisPDF(List<Sejour> sejours, Stage stage) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Enregistrer l'analyse des séjours");
        fileChooser.getExtensionFilters().add(
            new FileChooser.ExtensionFilter("PDF Files", "*.pdf")
        );
        fileChooser.setInitialFileName("analyse_sejours_" + LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyyMMdd_HHmmss")) + ".pdf");
        
        File file = fileChooser.showSaveDialog(stage);
        if (file != null) {
            try {
                PdfWriter writer = new PdfWriter(file);
                PdfDocument pdf = new PdfDocument(writer);
                Document document = new Document(pdf);
                
                // Add title
                Paragraph title = new Paragraph("Analyse des Séjours")
                    .setTextAlignment(TextAlignment.CENTER)
                    .setFontSize(20)
                    .setBold();
                document.add(title);
                
                // Add date
                Paragraph date = new Paragraph("Généré le: " + LocalDateTime.now().format(DATE_FORMATTER))
                    .setTextAlignment(TextAlignment.CENTER)
                    .setFontSize(12);
                document.add(date);
                
                // Add space
                document.add(new Paragraph("\n"));
                
                // Add summary statistics
                addSummaryStatistics(document, sejours);
                
                // Add detailed table
                addDetailedTable(document, sejours);
                
                document.close();
                
                // Show success message
                AlertUtil.showInformation(stage, "Succès", "Le PDF a été généré avec succès !");
            } catch (FileNotFoundException e) {
                AlertUtil.showError(stage, "Erreur", "Erreur lors de la génération du PDF: " + e.getMessage());
            }
        }
    }
    
    private void addSummaryStatistics(Document document, List<Sejour> sejours) {
        // Calculate statistics
        double totalFrais = sejours.stream().mapToDouble(Sejour::getFraisSejour).sum();
        double totalExtras = sejours.stream().mapToDouble(Sejour::getPrixExtras).sum();
        double totalRevenue = totalFrais + totalExtras;
        
        // Group by type
        Map<String, Long> countByType = sejours.stream()
            .collect(Collectors.groupingBy(Sejour::getTypeSejour, Collectors.counting()));
        
        // Group by payment status
        Map<String, Long> countByPaymentStatus = sejours.stream()
            .collect(Collectors.groupingBy(Sejour::getStatutPaiement, Collectors.counting()));
        
        // Create summary table
        Table summaryTable = new Table(UnitValue.createPercentArray(2)).useAllAvailableWidth();
        summaryTable.addCell(new Cell().add(new Paragraph("Statistiques Générales")).setBold());
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
        Table typeTable = new Table(UnitValue.createPercentArray(2)).useAllAvailableWidth();
        typeTable.addCell(new Cell().add(new Paragraph("Distribution par Type")).setBold());
        typeTable.addCell(new Cell().add(new Paragraph("")));
        
        countByType.forEach((type, count) -> {
            typeTable.addCell(new Cell().add(new Paragraph(type)));
            typeTable.addCell(new Cell().add(new Paragraph(String.valueOf(count))));
        });
        
        document.add(typeTable);
        document.add(new Paragraph("\n"));
        
        // Add payment status distribution
        Table paymentTable = new Table(UnitValue.createPercentArray(2)).useAllAvailableWidth();
        paymentTable.addCell(new Cell().add(new Paragraph("Distribution par Statut de Paiement")).setBold());
        paymentTable.addCell(new Cell().add(new Paragraph("")));
        
        countByPaymentStatus.forEach((status, count) -> {
            paymentTable.addCell(new Cell().add(new Paragraph(status)));
            paymentTable.addCell(new Cell().add(new Paragraph(String.valueOf(count))));
        });
        
        document.add(paymentTable);
        document.add(new Paragraph("\n"));
    }
    
    private void addDetailedTable(Document document, List<Sejour> sejours) {
        Table table = new Table(UnitValue.createPercentArray(8)).useAllAvailableWidth();
        
        // Add headers
        table.addHeaderCell(new Cell().add(new Paragraph("ID")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Date Entrée")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Date Sortie")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Type")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Frais")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Extras")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Paiement")).setBold());
        table.addHeaderCell(new Cell().add(new Paragraph("Statut")).setBold());
        
        // Add data rows
        for (Sejour sejour : sejours) {
            table.addCell(new Cell().add(new Paragraph(String.valueOf(sejour.getId()))));
            table.addCell(new Cell().add(new Paragraph(sejour.getDateEntree() != null ? 
                sejour.getDateEntree().format(DATE_FORMATTER) : "")));
            table.addCell(new Cell().add(new Paragraph(sejour.getDateSortie() != null ? 
                sejour.getDateSortie().format(DATE_FORMATTER) : "")));
            table.addCell(new Cell().add(new Paragraph(sejour.getTypeSejour())));
            table.addCell(new Cell().add(new Paragraph(String.format("%.2f €", sejour.getFraisSejour()))));
            table.addCell(new Cell().add(new Paragraph(String.format("%.2f €", sejour.getPrixExtras()))));
            table.addCell(new Cell().add(new Paragraph(sejour.getMoyenPaiement())));
            table.addCell(new Cell().add(new Paragraph(sejour.getStatutPaiement())));
        }
        
        document.add(table);
    }
} 