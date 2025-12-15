package util;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;

public class DataSource {

    private static DataSource instance;

    private Connection connection;

    // ---- MODIFY YOUR CREDENTIALS HERE ----
    private final String url = "jdbc:mysql://localhost:3306/app?useSSL=false&serverTimezone=UTC";
    private final String username = "root";
    private final String password = "My_SQL_R00t";
    // ---------------------------------------

    private DataSource() {
        try {
            // Load MySQL Driver
            Class.forName("com.mysql.cj.jdbc.Driver");

            // Establish connection
            connection = DriverManager.getConnection(url, username, password);
            System.out.println("✅ Database connection established successfully!");

        } catch (ClassNotFoundException e) {
            System.err.println("❌ MySQL JDBC Driver not found!");
            e.printStackTrace();

        } catch (SQLException e) {
            System.err.println("❌ Connection failed: " + e.getMessage());
            throw new RuntimeException("Failed to create database connection", e);
        }
    }

    // Singleton instance
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

    // Get connection and reopen if needed
    public Connection getConnection() {
        try {
            if (connection == null || connection.isClosed()) {
                connection = DriverManager.getConnection(url, username, password);
            }
        } catch (SQLException e) {
            System.err.println("❌ Could not reopen database connection!");
            e.printStackTrace();
        }
        return connection;
    }
    public static void setInstance(DataSource ds) {
        instance = ds;
    }

}
