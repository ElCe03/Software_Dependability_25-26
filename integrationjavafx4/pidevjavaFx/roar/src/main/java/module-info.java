module org.example.roar {
    // JavaFX Modules
    requires javafx.fxml;
    requires javafx.swing;
    requires javafx.web;
    requires javafx.graphics;
    // Jakarta Mail
    requires jakarta.mail;

    // Security & Hashing
    requires jbcrypt;

    // JSON & Serialization
    requires com.fasterxml.jackson.databind;
    requires org.json;
    requires com.google.protobuf;

    // Email & Preferences
    // Pour utiliser MailService ailleurs
    exports service;
    requires java.prefs;

    // Database & Persistence
    requires jakarta.persistence;
    requires mysql.connector.j;

    // Networking
    requires java.net.http;

    // Payments
    requires stripe.java;

    // PDF Generation
    requires itextpdf;
    requires org.apache.pdfbox;
    requires layout;
    requires de.jensd.fx.glyphs.fontawesome;
    requires com.google.zxing;
    requires com.google.zxing.javase;
    requires kernel;
    requires com.google.gson;  // For PDF layout (iText)

    // Open packages for reflection/FXML injection
    opens controllers to javafx.fxml;
    exports controllers;

    opens entite to javafx.base, com.google.gson;  // For TableView data binding
    exports entite;
    opens test to javafx.fxml, javafx.graphics;
    exports test;

}