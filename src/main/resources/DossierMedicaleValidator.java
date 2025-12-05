package util;

import entite.DossierMedicale;
import entite.User;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

public class DossierMedicaleValidator {
    
    public static class ValidationResult {
        private boolean isValid;
        private List<String> errors;
        
        public ValidationResult() {
            this.isValid = true;
            this.errors = new ArrayList<>();
        }
        
        public void addError(String error) {
            this.isValid = false;
            this.errors.add(error);
        }
        
        public boolean isValid() {
            return isValid;
        }
        
        public List<String> getErrors() {
            return errors;
        }
        
        public String getErrorMessage() {
            return String.join("\n", errors);
        }
    }
    
    public static ValidationResult validate(DossierMedicale dossier) {
        ValidationResult result = new ValidationResult();
        
        // Vérifier le patient
        if (dossier.getPatient() == null) {
            result.addError("Le patient est requis");
        } else {
            User patient = dossier.getPatient();
            if (patient.getId() <= 0) {
                result.addError("ID du patient invalide");
            }
            if (!patient.isPatient()) {
                result.addError("L'utilisateur sélectionné n'est pas un patient");
            }
        }
        
        // Vérifier le médecin
        if (dossier.getMedecin() == null) {
            result.addError("Le médecin est requis");
        } else {
            User medecin = dossier.getMedecin();
            if (medecin.getId() <= 0) {
                result.addError("ID du médecin invalide");
            }
            if (!medecin.isMedecin()) {
                result.addError("L'utilisateur sélectionné n'est pas un médecin");
            }
        }
        
        // Vérifier la date de création
        if (dossier.getDateDeCreation() == null) {
            result.addError("La date de création est requise");
        } else {
            LocalDateTime dateCreation = dossier.getDateDeCreation();
            if (dateCreation.isAfter(LocalDateTime.now())) {
                result.addError("La date de création ne peut pas être dans le futur");
            }
        }
        
        // Vérifier l'historique des maladies
        String historique = dossier.getHistoriqueDesMaladies();
        if (historique == null || historique.trim().isEmpty()) {
            result.addError("L'historique des maladies est requis");
        } else if (historique.length() > 1000) {
            result.addError("L'historique des maladies ne peut pas dépasser 1000 caractères");
        }
        
        // Vérifier les opérations passées
        String operations = dossier.getOperationsPassees();
        if (operations == null || operations.trim().isEmpty()) {
            result.addError("Les opérations passées sont requises");
        } else if (operations.length() > 1000) {
            result.addError("Les opérations passées ne peuvent pas dépasser 1000 caractères");
        }
        
        // Vérifier les consultations passées
        String consultations = dossier.getConsultationsPassees();
        if (consultations == null || consultations.trim().isEmpty()) {
            result.addError("Les consultations passées sont requises");
        } else if (consultations.length() > 1000) {
            result.addError("Les consultations passées ne peuvent pas dépasser 1000 caractères");
        }
        
        // Vérifier le statut du dossier
        String statut = dossier.getStatutDossier();
        if (statut == null || statut.trim().isEmpty()) {
            result.addError("Le statut du dossier est requis");
        } else if (!isValidStatut(statut)) {
            result.addError("Le statut du dossier est invalide");
        }
        
        // Vérifier les notes
        String notes = dossier.getNotes();
        if (notes != null) {
            notes = notes.trim();
            if (notes.length() > 500) {
                result.addError("Les notes ne peuvent pas dépasser 500 caractères");
            }
            // Vérifier le contenu des notes
            if (notes.contains("<script>") || notes.contains("javascript:")) {
                result.addError("Les notes contiennent du code malveillant");
            }
            // Vérifier les caractères spéciaux
            if (!notes.matches("^[\\p{L}\\p{N}\\p{P}\\p{Z}\\s]*$")) {
                result.addError("Les notes contiennent des caractères non autorisés");
            }
        }
        
        // Vérifier l'image
        String image = dossier.getImage();
        if (image != null && !image.isEmpty()) {
            if (!isValidImageFormat(image)) {
                result.addError("Le format de l'image n'est pas valide (formats acceptés: jpg, jpeg, png)");
            }
        }
        
        return result;
    }
    
    private static boolean isValidStatut(String statut) {
        return statut.equals("Actif") || 
               statut.equals("Archivé") || 
               statut.equals("En attente");
    }
    
    private static boolean isValidImageFormat(String filename) {
        String lowerFilename = filename.toLowerCase();
        return lowerFilename.endsWith(".jpg") || 
               lowerFilename.endsWith(".jpeg") || 
               lowerFilename.endsWith(".png");
    }
} 