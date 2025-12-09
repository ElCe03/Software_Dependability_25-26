package form;

import javax.swing.*;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import util.DataSource;

public class FormulaireMedecin {
    
    public static void afficherFormulaire(int userId) {
        String specialite = JOptionPane.showInputDialog("Spécialité du médecin :");
        String telephone = JOptionPane.showInputDialog("Numéro de téléphone :");

        String req = "UPDATE users SET specialite = ?, telephone = ? WHERE id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement pstmt = conn.prepareStatement(req)) {

            pstmt.setString(1, specialite);
            pstmt.setString(2, telephone);
            pstmt.setInt(3, userId);

            pstmt.executeUpdate();
            System.out.println("✅ Médecin mis à jour dans la table `users` !");

        } catch (SQLException e) {
            System.err.println("❌ Erreur SQL mise à jour médecin : " + e.getMessage());
        } catch (Exception e) {
            System.err.println("❌ Erreur générique : " + e.getMessage());
        }
    }
}
