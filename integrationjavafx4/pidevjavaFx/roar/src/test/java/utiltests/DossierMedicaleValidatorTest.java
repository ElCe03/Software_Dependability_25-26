package util;

import entite.DossierMedicale;
import entite.User;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.*;

class DossierMedicaleValidatorTest {

    private DossierMedicale dossier;
    private User validPatient;
    private User validMedecin;

    @BeforeEach
    void setUp() {
        validPatient = new User();
        validPatient.setId(1);
        validPatient.setType("patient");
        validPatient.setNom("PatientTest");

        validMedecin = new User();
        validMedecin.setId(2);
        validMedecin.setType("medecin");
        validMedecin.setNom("MedecinTest");

        dossier = new DossierMedicale();
        dossier.setPatient(validPatient);
        dossier.setMedecin(validMedecin);
        dossier.setDateDeCreation(LocalDateTime.now().minusMinutes(1)); 
        dossier.setHistoriqueDesMaladies("Rien à signaler");
        dossier.setOperationsPassees("Aucune");
        dossier.setConsultationsPassees("Visite de routine");
        dossier.setStatutDossier("Actif");
        dossier.setNotes("Patient en bonne santé.");
        dossier.setImage("scan.jpg");
    }

    @Test
    @DisplayName("Dossier valido: Deve passare senza errori")
    void testValidate_ValidDossier() {
        var result = DossierMedicaleValidator.validate(dossier);
        assertTrue(result.isValid(), "Un dossier valido non deve avere errori");
        assertTrue(result.getErrors().isEmpty());
    }

    @Test
    @DisplayName("Utenti null o ID invalidi")
    void testValidate_InvalidUsers() {
        dossier.setPatient(null);
        dossier.setMedecin(null);

        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("Le patient est requis"));
        assertTrue(result.getErrorMessage().contains("Le médecin est requis"));

        dossier.setPatient(new User()); 
        dossier.setMedecin(new User()); 
        
        result = DossierMedicaleValidator.validate(dossier);
        assertTrue(result.getErrorMessage().contains("ID du patient invalide"));
        assertTrue(result.getErrorMessage().contains("ID du médecin invalide"));
    }

    @Test
    @DisplayName("Ruoli utente errati (Scambio Medico/Paziente)")
    void testValidate_WrongUserRoles() {
        validPatient.setType("medecin"); 
        validMedecin.setType("patient");

        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("n'est pas un patient"), "Deve rilevare che il paziente ha il ruolo sbagliato");
        assertTrue(result.getErrorMessage().contains("n'est pas un médecin"), "Deve rilevare che il medico ha il ruolo sbagliato");
    }

    @Test
    @DisplayName("Data di creazione futura o nulla")
    void testValidate_DateLogic() {
        dossier.setDateDeCreation(null);
        var result = DossierMedicaleValidator.validate(dossier);
        assertTrue(result.getErrorMessage().contains("La date de création est requise"));

        dossier.setDateDeCreation(LocalDateTime.now().plusDays(1)); 
        result = DossierMedicaleValidator.validate(dossier);
        assertTrue(result.getErrorMessage().contains("ne peut pas être dans le futur"));
    }

    @Test
    @DisplayName("Campi testuali obbligatori vuoti")
    void testValidate_MandatoryStringsEmpty() {
        dossier.setHistoriqueDesMaladies("   "); 
        dossier.setOperationsPassees(null);
        dossier.setConsultationsPassees("");

        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("L'historique des maladies est requis"));
        assertTrue(result.getErrorMessage().contains("Les opérations passées sont requises"));
        assertTrue(result.getErrorMessage().contains("Les consultations passées sont requises"));
    }

    @Test
    @DisplayName("Boundary Test: Lunghezza massima stringhe (1000 char)")
    void testValidate_StringLengthBoundaries() {
        String longText = "a".repeat(1001); 
        dossier.setHistoriqueDesMaladies(longText);

        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("ne peut pas dépasser 1000 caractères"));

        dossier.setHistoriqueDesMaladies("a".repeat(1000));
        result = DossierMedicaleValidator.validate(dossier);
        assertTrue(result.isValid());
    }

    @ParameterizedTest
    @ValueSource(strings = {"Actif", "Archivé", "En attente"})
    @DisplayName("Stati validi")
    void testValidate_ValidStatuses(String status) {
        dossier.setStatutDossier(status);
        assertTrue(DossierMedicaleValidator.validate(dossier).isValid());
    }

    @Test
    @DisplayName("Stato invalido")
    void testValidate_InvalidStatus() {
        dossier.setStatutDossier("Cancellato"); 
        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("Le statut du dossier est invalide"));
    }

    @ParameterizedTest
    @ValueSource(strings = {
        "<script>alert('hack')</script>", 
        "javascript:void(0)", 
        "Click here <script src=...>"
    })
    @DisplayName("Security: Rilevamento XSS nelle note")
    void testValidate_SecurityXSS(String maliciousInput) {
        dossier.setNotes(maliciousInput);
        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("contiennent du code malveillant"));
    }

    @Test
    @DisplayName("Caratteri speciali non permessi nelle note")
    void testValidate_NotesSpecialChars() {
        dossier.setNotes("Nota con emoji 😊"); 
        var result = DossierMedicaleValidator.validate(dossier);
        

        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("caractères non autorisés"));
    }

    @Test
    @DisplayName("Notes troppo lunghe (>500)")
    void testValidate_NotesLength() {
        dossier.setNotes("a".repeat(501));
        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("Les notes ne peuvent pas dépasser 500 caractères"));
    }

    @ParameterizedTest
    @ValueSource(strings = {"image.jpg", "PHOTO.PNG", "scan.jpeg"})
    @DisplayName("Estensioni immagini valide (Case Insensitive)")
    void testValidate_ValidImages(String filename) {
        dossier.setImage(filename);
        assertTrue(DossierMedicaleValidator.validate(dossier).isValid());
    }

    @ParameterizedTest
    @ValueSource(strings = {"virus.exe", "report.pdf", "image", "image.gif"})
    @DisplayName("Estensioni immagini non valide")
    void testValidate_InvalidImages(String filename) {
        dossier.setImage(filename);
        var result = DossierMedicaleValidator.validate(dossier);
        assertFalse(result.isValid());
        assertTrue(result.getErrorMessage().contains("format de l'image n'est pas valide"));
    }
    @Test
    @DisplayName("Accumulo errori: Deve riportare tutti gli errori presenti contemporaneamente")
    void testValidate_MultipleErrors() {
        dossier.setPatient(null);                                   
        dossier.setDateDeCreation(LocalDateTime.now().plusDays(1)); 
        dossier.setStatutDossier("Cancellato");                     

        var result = DossierMedicaleValidator.validate(dossier);
        
        assertFalse(result.isValid());
        assertEquals(3, result.getErrors().size(), "Deve rilevare tutti e 3 gli errori, non fermarsi al primo");
        
        String allErrors = result.getErrorMessage();
        assertTrue(allErrors.contains("Le patient est requis"));
        assertTrue(allErrors.contains("futur"));
        assertTrue(allErrors.contains("statut du dossier est invalide"));
    }

    @Test
    @DisplayName("Campi opzionali nulli o vuoti devono essere considerati validi")
    void testValidate_OptionalFields() {
        dossier.setNotes(null);
        dossier.setImage(null);
        assertTrue(DossierMedicaleValidator.validate(dossier).isValid(), "Note e Immagine a NULL devono essere validi");

        dossier.setNotes("");
        dossier.setImage("");
        assertTrue(DossierMedicaleValidator.validate(dossier).isValid(), "Note e Immagine vuoti devono essere validi");
    }
}