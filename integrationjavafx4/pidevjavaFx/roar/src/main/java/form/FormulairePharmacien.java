package form;

import javax.swing.*;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import util.DataSource;

public class FormulairePharmacien {
    
    public static void afficherFormulaire(int userId) {
        String telephone = JOptionPane.showInputDialog("Numéro de téléphone du pharmacien :");

        String req = "UPDATE users SET telephone = ? WHERE id = ?";

        try (Connection conn = DataSource.getInstance().getConnection();
             PreparedStatement pstmt = conn.prepareStatement(req)) {

            pstmt.setString(1, telephone);
            pstmt.setInt(2, userId);

            pstmt.executeUpdate();
            System.out.println("✅ Pharmacien mis à jour dans la table `users` !");

        } catch (SQLException e) {
            System.err.println("❌ Erreur SQL mise à jour pharmacien : " + e.getMessage());
        } catch (Exception e) {
            System.err.println("❌ Erreur générique : " + e.getMessage());
        }
    }
}
