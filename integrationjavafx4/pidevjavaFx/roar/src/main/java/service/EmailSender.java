package service;

import jakarta.mail.*;
import jakarta.mail.internet.InternetAddress;
import jakarta.mail.internet.MimeMessage;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class EmailSender {

    private static String EMAIL;
    private static String PASSWORD;

    static {
        try (InputStream input = EmailSender.class.getClassLoader().getResourceAsStream("config.properties")) {
            Properties prop = new Properties();

            if (input == null) {
                System.out.println("Spiacente, impossibile trovare config.properties");
            } else {
                prop.load(input);

                EMAIL = prop.getProperty("email.username");
                PASSWORD = prop.getProperty("email.password");
            }
        } catch (IOException ex) {
            System.out.println("Errore durante il caricamento del file di configurazione.");
        }
    }

    private static Session getSession() {
        Properties props = new Properties();
        props.put("mail.smtp.host", "smtp.gmail.com");
        props.put("mail.smtp.port", "587");
        props.put("mail.smtp.auth", "true");
        props.put("mail.smtp.starttls.enable", "true");
        props.put("mail.smtp.ssl.checkserveridentity", "true");

        return Session.getInstance(props, new Authenticator() {
            @Override
            protected PasswordAuthentication getPasswordAuthentication() {
                return new PasswordAuthentication(EMAIL, PASSWORD);
            }
        });
    }

    public static boolean sendEmail(String to, String subject, String content) {
        if (EMAIL == null || PASSWORD == null || EMAIL.isEmpty() || PASSWORD.isEmpty()) {
            System.out.println("Errore: Credenziali Gmail non impostate o file config.properties non letto!");
            return false;
        }

        try {
            Message message = new MimeMessage(getSession());
            message.setFrom(new InternetAddress(EMAIL));
            message.setRecipients(Message.RecipientType.TO, InternetAddress.parse(to));
            message.setSubject(subject);
            message.setText(content);

            Transport.send(message);
            System.out.println("Email inviata con successo a " + to);
            return true;
        } catch (MessagingException e) {
            System.out.println("Errore nell'invio dell'email: " + e.getMessage());
            e.printStackTrace();
            return false;
        }
    }

    public static void envoyerEmailInscription(String email, String nom, String password, String type) {
        String subject = "Bienvenue sur ClinicCare!";
        String content = "Bonjour " + nom + ",\n\n" +
                "Bienvenue sur ClinicCare ! Vous êtes inscrit en tant que " + type + ".\n" +
                "Vos identifiants :\n" +
                "Email : " + email + "\n" +
                "Mot de passe : " + password + "\n\n" +
                "Cordialement,\n" +
                "L'équipe ClinicCare.";

        sendEmail(email, subject, content);
    }
}

