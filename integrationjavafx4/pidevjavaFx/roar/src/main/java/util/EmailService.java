package util;

import jakarta.mail.*;
import jakarta.mail.internet.*;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;
import javafx.application.Platform;
import javafx.concurrent.Task;

public class EmailService {
    private static final Logger LOGGER = Logger.getLogger(EmailService.class.getName());
    private static final Properties CONFIG_PROPS = loadConfig();

    // Configuration SMTP
    private static final String SMTP_HOST = getConfig("smtp.host", "sandbox.smtp.mailtrap.io");
    private static final String SMTP_PORT = getConfig("smtp.port", "2525");
    private static final String SMTP_USERNAME = getConfig("smtp.username", "9361312ac3db7b");
    private static final String SMTP_PASSWORD = getConfig("smtp.password", "2b31585dc32d1c");
    private static final String SENDER_EMAIL = getConfig("sender.email", "eyah5268@gmail.com");
    private static final String SENDER_NAME = getConfig("sender.name", "eya");

    // Propriétés SMTP
    private static final Properties SMTP_PROPS = new Properties();
    static {
        SMTP_PROPS.put("mail.smtp.auth", "true");
        SMTP_PROPS.put("mail.smtp.starttls.enable", "true");
        SMTP_PROPS.put("mail.smtp.host", SMTP_HOST);
        SMTP_PROPS.put("mail.smtp.port", SMTP_PORT);
        SMTP_PROPS.put("mail.smtp.ssl.protocols", "TLSv1.2");
        SMTP_PROPS.put("mail.smtp.connectiontimeout", "5000");
        SMTP_PROPS.put("mail.smtp.timeout", "5000");
        SMTP_PROPS.put("mail.debug", "true"); // Activation des logs
    }

    private static Properties loadConfig() {
        Properties props = new Properties();
        try (InputStream input = EmailService.class.getClassLoader().getResourceAsStream("mailtrap.properties")) {
            if (input != null) {
                props.load(input);
            }
        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Erreur de chargement du fichier de configuration", e);
        }
        return props;
    }

    private static String getConfig(String key, String defaultValue) {
        return CONFIG_PROPS.getProperty(key, defaultValue);
    }

    public static void sendReservationEmail(
            String recipientEmail,
            String salleName,
            String dateDebut,
            String dateFin,
            String typeSalle,
            String status,
            Runnable onSuccess,
            Runnable onFailure
    ) {
        Task<Void> emailTask = new Task<Void>() {
            @Override
            protected Void call() throws Exception {
                try {
                    // Ensure SSL server identity is checked for MITM protection
                    SMTP_PROPS.put("mail.smtp.ssl.checkserveridentity", "true");

                    Authenticator auth = new Authenticator() {
                        @Override
                        protected PasswordAuthentication getPasswordAuthentication() {
                            return new PasswordAuthentication(SMTP_USERNAME, SMTP_PASSWORD);
                        }
                    };

                    Session session = Session.getInstance(SMTP_PROPS, auth);

                    Message message = new MimeMessage(session);
                    message.setFrom(new InternetAddress(SENDER_EMAIL, SENDER_NAME));
                    message.setRecipients(Message.RecipientType.TO, InternetAddress.parse(recipientEmail));
                    message.setSubject("Confirmation de Réservation");

                    // Partie texte
                    String textContent = String.format(
                            "Bonjour,\n\nVotre réservation pour la salle %s a été confirmée.\n\n" +
                                    "Détails :\n- Date : %s à %s\n- Type : %s\n- Statut : %s\n\n" +
                                    "Cordialement,\n%s",
                            salleName, dateDebut, dateFin, typeSalle, status, SENDER_NAME
                    );

                    // Partie HTML
                    String htmlContent = String.format(
                            "<html><body>" +
                                    "<h2>Confirmation de Réservation</h2>" +
                                    "<p>Bonjour,</p>" +
                                    "<p>Votre réservation pour la salle <strong>%s</strong> a été confirmée.</p>" +
                                    "<ul>" +
                                    "<li><strong>Date :</strong> %s à %s</li>" +
                                    "<li><strong>Type :</strong> %s</li>" +
                                    "<li><strong>Statut :</strong> %s</li>" +
                                    "</ul>" +
                                    "<p>Cordialement,<br>%s</p>" +
                                    "</body></html>",
                            salleName, dateDebut, dateFin, typeSalle, status, SENDER_NAME
                    );

                    MimeMultipart multipart = new MimeMultipart("alternative");

                    MimeBodyPart textPart = new MimeBodyPart();
                    textPart.setText(textContent, "UTF-8");

                    MimeBodyPart htmlPart = new MimeBodyPart();
                    htmlPart.setContent(htmlContent, "text/html; charset=UTF-8");

                    multipart.addBodyPart(textPart);
                    multipart.addBodyPart(htmlPart);

                    message.setContent(multipart);
                    Transport.send(message);

                    Platform.runLater(onSuccess);
                } catch (Exception e) {
                    LOGGER.log(Level.SEVERE, "Erreur d'envoi d'email", e);
                    Platform.runLater(onFailure);
                }
                return null;
            }
        };

        new Thread(emailTask).start();
    }

    public static class EmailException extends Exception {
        public EmailException(String message, Throwable cause) {
            super(message, cause);
        }
    }
}