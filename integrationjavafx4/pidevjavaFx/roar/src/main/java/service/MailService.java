package service;

import jakarta.mail.*;
import jakarta.mail.internet.*;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class MailService {

    private static String FROM_EMAIL;
    private static String PASSWORD;

    static {
        try (InputStream input = MailService.class.getClassLoader().getResourceAsStream("config.properties")) {
            Properties prop = new Properties();

            if (input == null) {
                System.err.println("❌ Spiacente, impossibile trovare config.properties");
            } else {
                prop.load(input);

                FROM_EMAIL = prop.getProperty("email.username");
                PASSWORD = prop.getProperty("email.password");
            }
        } catch (IOException ex) {
            System.err.println("❌ Errore durante il caricamento del file di configurazione.");
            ex.printStackTrace();
        }
    }

    public static void sendEmail(String toEmail, String subject, String body) {
        if (FROM_EMAIL == null || PASSWORD == null) {
            System.err.println("❌ Errore: Credenziali email non caricate dal file config.properties.");
            return;
        }

        Properties props = new Properties();
        props.put("mail.smtp.host", "smtp.gmail.com"); // Serveur SMTP
        props.put("mail.smtp.port", "587"); // Port TLS
        props.put("mail.smtp.auth", "true");
        props.put("mail.smtp.starttls.enable", "true"); // TLS

        Session session = Session.getInstance(props, new Authenticator() {
            @Override
            protected PasswordAuthentication getPasswordAuthentication() {
                return new PasswordAuthentication(FROM_EMAIL, PASSWORD);
            }
        });

        try {
            Message message = new MimeMessage(session);
            message.setFrom(new InternetAddress(FROM_EMAIL, "Clinique"));
            message.setRecipients(Message.RecipientType.TO, InternetAddress.parse(toEmail));
            message.setSubject(subject);
            message.setText(body);

            Transport.send(message);
            System.out.println("📩 Email envoyé avec succès !");
        } catch (Exception e) {
            System.err.println("❌ Erreur d'envoi de l'email : " + e.getMessage());
            e.printStackTrace();
        }
    }
}
