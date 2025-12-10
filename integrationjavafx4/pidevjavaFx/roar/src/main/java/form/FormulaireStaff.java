package form;

import javax.swing.*;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import util.DataSource;

public class FormulaireStaff {
    
    public static void afficherFormulaire(int userId) {
        String telephone = JOptionPane.showInputDialog("Numéro de téléphone du staff :");

        String req = "UPDATE users SET telephone = ? WHERE id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement pstmt = conn.prepareStatement(req)) {

            pstmt.setString(1, telephone);
            pstmt.setInt(2, userId);

            pstmt.executeUpdate();
            System.out.println("✅ Staff mis à jour dans la table `users` !");

        } catch (SQLException e) { 
            System.err.println("❌ Erreur mise à jour staff : " + e.getMessage());
        } catch (Exception e) {
            System.err.println("❌ Erreur générique : " + e.getMessage());
        }
    }
}
