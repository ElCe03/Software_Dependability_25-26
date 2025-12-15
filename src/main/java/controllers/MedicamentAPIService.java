package controllers;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.text.Normalizer;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

public class MedicamentAPIService {

    private static final Map<String, String> FRENCH_TO_ENGLISH = createTranslationMap();
    private static final Map<String, String> API_CACHE = Collections.synchronizedMap(
            new LinkedHashMap<String, String>(100, 0.75f, true) {
                protected boolean removeEldestEntry(Map.Entry<String, String> eldest) {
                    return size() > 100;
                }
            });

    private static Map<String, String> createTranslationMap() {
        Map<String, String> map = new LinkedHashMap<>();
        // Médicaments génériques
        map.put("ibuprofène", "ibuprofen");
        map.put("paracétamol", "acetaminophen");
        map.put("aspirine", "aspirin");
        map.put("amoxicilline", "amoxicillin");
        map.put("oméprazole", "omeprazole");

        // Marques françaises
        map.put("doliprane", "acetaminophen");
        map.put("kardegic", "aspirin");
        map.put("ventoline", "albuterol");
        map.put("tahor", "atorvastatin");
        map.put("plavix", "clopidogrel");
        map.put("coumadine", "warfarin");

        // Psychotropes
        map.put("lexomil", "bromazepam");
        map.put("xanax", "alprazolam");

        return map;
    }

    public String chercherMedicament(String nomMedicament) throws Exception {
        return executeRechercheAPI(nomMedicament,
                "openfda.brand_name:%1$s+openfda.generic_name:%1$s", 1);
    }

    public String chercherMedicamentSimple(String nomMedicament) throws Exception {
        return executeRechercheAPI(nomMedicament, "%1$s", 1);
    }

    public String chercherMedicamentComplet(String nomMedicament) throws Exception {
        String searchTerm = normalizeAndTranslateTerm(nomMedicament);
        String encodedName = URLEncoder.encode(searchTerm, StandardCharsets.UTF_8.toString())
                .replace("+", "%20"); // Correction critique pour l'API FDA

        String apiUrl = String.format(
                "https://api.fda.gov/drug/label.json?search="
                        + "(openfda.brand_name:\"%1$s\"+OR+openfda.generic_name:\"%1$s\")"
                        + "&limit=10",
                encodedName
        );

        return executeAPICall(apiUrl);
    }

    private String executeRechercheAPI(String nomMedicament, String queryPattern, int limit) throws Exception {
        String searchTerm = normalizeAndTranslateTerm(nomMedicament);
        String encodedName = URLEncoder.encode(searchTerm, StandardCharsets.UTF_8);
        String apiUrl = String.format(
                "https://api.fda.gov/drug/label.json?search=" + queryPattern + "&limit=%d",
                encodedName, limit
        );
        return executeAPICall(apiUrl);
    }

    private String normalizeAndTranslateTerm(String term) {
        String normalized = Normalizer.normalize(term, Normalizer.Form.NFD)
                .replaceAll("[\\p{InCombiningDiacriticalMarks}]", "")
                .toLowerCase()
                .replaceAll("[^a-z0-9]", "");
        return FRENCH_TO_ENGLISH.getOrDefault(normalized, normalized);
    }

    private String executeAPICall(String apiUrl) throws Exception {
        if (API_CACHE.containsKey(apiUrl)) {
            System.out.println("Cache hit for: " + apiUrl);
            return API_CACHE.get(apiUrl);
        }

        System.out.println("API call: " + apiUrl);
        URL url = new URL(apiUrl);
        HttpURLConnection conn = (HttpURLConnection) url.openConnection();
        conn.setRequestMethod("GET");
        conn.setConnectTimeout(5000);
        conn.setReadTimeout(5000);
        conn.setRequestProperty("Accept", "application/json");

        StringBuilder response = new StringBuilder();
        int responseCode = conn.getResponseCode();

        if (responseCode == 200) {
            try (BufferedReader reader = new BufferedReader(
                    new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    response.append(line);
                }
            }
            API_CACHE.put(apiUrl, response.toString());
            System.out.println("API response success");
        } else {
            response.append("{\"error\":\"API response code ").append(responseCode).append("\"}");
            System.out.println("API error: " + responseCode);
        }

        conn.disconnect();
        return response.toString();
    }

    public void clearCache() {
        API_CACHE.clear();
        System.out.println("Cache cleared");
    }
}