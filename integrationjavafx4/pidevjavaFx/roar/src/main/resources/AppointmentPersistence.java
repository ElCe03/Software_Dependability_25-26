package util;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;
import entite.Appointment;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Type;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

public class AppointmentPersistence {
    private static final String APPOINTMENTS_FILE = "appointments.json";
    private static final Gson gson = new GsonBuilder()
            .registerTypeAdapter(LocalDateTime.class, new LocalDateTimeAdapter())
            .create();

    public static void saveAppointments(List<Appointment> appointments) {
        try (FileWriter writer = new FileWriter(APPOINTMENTS_FILE)) {
            gson.toJson(appointments, writer);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static List<Appointment> loadAppointments() {
        List<Appointment> appointments = new ArrayList<>();
        File file = new File(APPOINTMENTS_FILE);
        if (!file.exists()) {
            return appointments;
        }

        try (FileReader reader = new FileReader(file)) {
            Type listType = new TypeToken<ArrayList<Appointment>>(){}.getType();
            appointments = gson.fromJson(reader, listType);
        } catch (IOException e) {
            e.printStackTrace();
        }

        return appointments;
    }
} 