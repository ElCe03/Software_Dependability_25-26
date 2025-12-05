package controllers;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.stage.Stage;

import java.io.IOException;

public class Core {
    private final String DATA_PATH = "C:\\Users\\seddi\\Downloads\\archive (3)\\Disease_symptom_and_patient_profile_dataset.csv";
    private final Map<String, Integer> diseaseCounts = new HashMap<>();
    private final Map<String, Map<String, Map<String, Integer>>> symptomValueCounts = new HashMap<>();
    private final List<String> symptomNames = new ArrayList<>();
    private int totalCases = 0;
    private final double LAPLACE_K = 1.0;

    public Core() {
        loadData();
        System.out.println("Initialized with " + diseaseCounts.size() + " diseases and "
                + symptomNames.size() + " symptoms");
    }

    private void loadData() {
        try (BufferedReader br = new BufferedReader(new FileReader(DATA_PATH))) {
            String[] headers = br.readLine().split(",");
            symptomNames.addAll(Arrays.asList(headers).subList(1, headers.length-1));

            String line;
            while ((line = br.readLine()) != null) {
                String[] values = line.split(",(?=(?:[^\"]*\"[^\"]*\")*[^\"]*$)", -1);
                if (values.length < headers.length) continue;

                String disease = values[0].trim();
                diseaseCounts.put(disease, diseaseCounts.getOrDefault(disease, 0) + 1);
                totalCases++;

                for (int i = 0; i < symptomNames.size(); i++) {
                    String symptom = symptomNames.get(i);
                    String value = values[i+1].trim().replaceAll("^\"|\"$", "").trim();
                    value = value.isEmpty() ? "Unknown" : value;
                    value = normalizeValue(symptom, value);

                    symptomValueCounts
                            .computeIfAbsent(symptom, k -> new HashMap<>())
                            .computeIfAbsent(value, k -> new HashMap<>())
                            .merge(disease, 1, Integer::sum);
                }
            }
        } catch (IOException e) {
            System.err.println("Data loading failed: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private String normalizeValue(String symptom, String value) {
        value = value.trim();
        if (symptom.equalsIgnoreCase("Gender")) {
            if (value.equalsIgnoreCase("m") || value.equalsIgnoreCase("male")) return "Male";
            if (value.equalsIgnoreCase("f") || value.equalsIgnoreCase("female")) return "Female";
            return "Other";
        }
        else if (symptom.equalsIgnoreCase("Fever") ||
                symptom.equalsIgnoreCase("Cough") ||
                symptom.equalsIgnoreCase("Fatigue") ||
                symptom.equalsIgnoreCase("Difficulty Breathing")) {
            if (value.equalsIgnoreCase("y") || value.equalsIgnoreCase("yes") || value.equals("1")) return "Yes";
            if (value.equalsIgnoreCase("n") || value.equalsIgnoreCase("no") || value.equals("0")) return "No";
            return "Unknown";
        }
        else if (symptom.equalsIgnoreCase("Cholesterol Level")) {
            if (value.equalsIgnoreCase("normal") || value.contains("<200")) return "Normal";
            if (value.toLowerCase().contains("borderline")) return "Borderline High";
            if (value.toLowerCase().contains("very high")) return "Very High";
            if (value.toLowerCase().contains("high")) return "High";
            return "Unknown";
        }
        else if (symptom.equalsIgnoreCase("Blood Pressure")) {
            if (value.equalsIgnoreCase("normal") || value.contains("<120")) return "Normal";
            if (value.toLowerCase().contains("elevated")) return "Elevated";
            if (value.toLowerCase().contains("very high")) return "Very High";
            if (value.toLowerCase().contains("high")) return "High";
            return "Unknown";
        }
        else if (symptom.equalsIgnoreCase("Age")) {
            try {
                int age = Integer.parseInt(value);
                if (age < 20) return "Under 20";
                if (age < 30) return "20-29";
                if (age < 40) return "30-39";
                if (age < 50) return "40-49";
                if (age < 60) return "50-59";
                if (age < 70) return "60-69";
                return "70+";
            } catch (NumberFormatException e) {
                return value; // Return original if not a number
            }
        }
        return value;
    }

    public Map<String, Double> predict(Map<String, String> symptomsInput) {
        Map<String, Double> scores = new HashMap<>();
        int totalDiseases = diseaseCounts.size();

        for (String disease : diseaseCounts.keySet()) {
            double diseasePrior = (double)(diseaseCounts.get(disease) + LAPLACE_K)
                    / (totalCases + LAPLACE_K * totalDiseases);
            double logScore = Math.log(diseasePrior);

            for (Map.Entry<String, String> entry : symptomsInput.entrySet()) {
                String symptom = entry.getKey();
                String value = entry.getValue();

                int symptomValueCount = symptomValueCounts
                        .getOrDefault(symptom, Collections.emptyMap())
                        .getOrDefault(value, Collections.emptyMap())
                        .getOrDefault(disease, 0);

                int diseaseTotal = diseaseCounts.get(disease);
                int valueOptions = symptomValueCounts
                        .getOrDefault(symptom, Collections.emptyMap())
                        .size();

                double likelihood = (symptomValueCount + LAPLACE_K)
                        / (diseaseTotal + LAPLACE_K * valueOptions);
                logScore += Math.log(likelihood);
            }
            scores.put(disease, logScore);
        }

        return normalizeScores(scores);
    }

    private Map<String, Double> normalizeScores(Map<String, Double> logScores) {
        if (logScores.isEmpty()) return new LinkedHashMap<>();

        double maxLog = Collections.max(logScores.values());
        double sum = logScores.values().stream()
                .mapToDouble(score -> Math.exp(score - maxLog))
                .sum();

        return logScores.entrySet().stream()
                .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                .collect(Collectors.toMap(
                        Map.Entry::getKey,
                        e -> (Math.exp(e.getValue() - maxLog) / sum) * 100,
                        (a, b) -> a,
                        LinkedHashMap::new
                ));
    }

    public List<String> getSymptoms() {
        return Collections.unmodifiableList(symptomNames);
    }




}