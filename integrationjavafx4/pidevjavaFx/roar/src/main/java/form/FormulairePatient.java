package form;

import javax.swing.*;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.time.LocalDate;
import java.time.format.DateTimeParseException;
import util.DataSource;

public class FormulairePatient {
    
    public static void afficherFormulaire(int userId) {
        String adresse = JOptionPane.showInputDialog("Adresse du patient :");
        String telephone = JOptionPane.showInputDialog("Numéro de téléphone :");
        String dateNaissanceStr = JOptionPane.showInputDialog("Date de naissance (format: yyyy-MM-dd) :");

        String req = "UPDATE users SET adresse = ?, telephone = ?, date_naissance = ? WHERE id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement pstmt = conn.prepareStatement(req)) {

            pstmt.setString(1, adresse);
            pstmt.setString(2, telephone);
            
            pstmt.setDate(3, java.sql.Date.valueOf(LocalDate.parse(dateNaissanceStr)));
            
            pstmt.setInt(4, userId);

            pstmt.executeUpdate();
            System.out.println("✅ Patient mis à jour dans la table `users` !");

        } catch (SQLException e) {
            System.err.println("❌ Erreur SQL mise à jour patient : " + e.getMessage());
        } catch (DateTimeParseException e) {
            System.err.println("❌ Erreur format date : " + e.getMessage());
            JOptionPane.showMessageDialog(null, "Format de date invalide ! Utilisez yyyy-MM-dd", "Erreur", JOptionPane.ERROR_MESSAGE);
        } catch (Exception e) {
            System.err.println("❌ Erreur générique : " + e.getMessage());
        }
    }
}
