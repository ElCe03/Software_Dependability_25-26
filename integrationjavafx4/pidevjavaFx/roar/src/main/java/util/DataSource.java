package util;

import java.io.IOException;
import java.io.InputStream;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Properties;

public class DataSource {
    private String url;
    private String username;
    private String password;
    
    private Connection connection;
    private static DataSource instance;

    private DataSource() {
        loadProperties();

        try {
            Class.forName("com.mysql.cj.jdbc.Driver");

            connection = DriverManager.getConnection(url, username, password);
            System.out.println("Database connection established successfully!");
            
        } catch (ClassNotFoundException e) {
            System.err.println("MySQL JDBC Driver not found!");
            e.printStackTrace();
        } catch (SQLException e) {
            System.err.println("Connection failed! Check output console");
            e.printStackTrace();
            throw new RuntimeException("Failed to create database connection", e);
        }
    }

    private void loadProperties() {
        try (InputStream input = getClass().getClassLoader().getResourceAsStream("config.properties")) {
            Properties prop = new Properties();

            if (input == null) {
                System.err.println("❌ Errore: Impossibile trovare config.properties");
                throw new RuntimeException("config.properties not found");
            }

            prop.load(input);

            this.url = prop.getProperty("db.url");
            this.username = prop.getProperty("db.username");
            this.password = prop.getProperty("db.password");

            if (this.url == null || this.username == null || this.password == null) {
                throw new RuntimeException("Configurazioni database mancanti nel file properties!");
            }

        } catch (IOException ex) {
            System.err.println("❌ Errore durante la lettura del file di configurazione.");
            throw new RuntimeException("Failed to load database configuration", ex);
        }
    }

    public static DataSource getInstance() {
        if (instance == null) {
            synchronized (DataSource.class) {
                if (instance == null) {
                    instance = new DataSource();
                }
            }
        }
        return instance;
    }

    public Connection getConnection() {
        try {
            if (connection == null || connection.isClosed()) {
                System.out.println("Reconnecting to database...");
                connection = DriverManager.getConnection(url, username, password);
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return connection;
    }
}

