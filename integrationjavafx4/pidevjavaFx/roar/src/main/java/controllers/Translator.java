package controllers;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.net.http.HttpRequest.BodyPublishers;
import java.util.concurrent.CompletableFuture;

public class Translator {
    private static final String API_URL = "https://libretranslate.de/translate";
    private static final HttpClient httpClient = HttpClient.newHttpClient();
    private static final int MAX_RETRIES = 2;
    private static final long RETRY_DELAY_MS = 500;
    private static boolean apiDisabled = false;
    private static int consecutiveFailures = 0;
    private static final int FAILURE_THRESHOLD = 3;

    public static void resetFailures() {
        consecutiveFailures = 0;
        apiDisabled = false;
    }

    public static CompletableFuture<String> translateAsync(String text, String sourceLang, String targetLang) {
        if (text == null || text.trim().isEmpty() || sourceLang.equals(targetLang)) {
            return CompletableFuture.completedFuture(text);
        }

        if (apiDisabled) {
            System.err.println("API disabled due to repeated failures, using fallback");
            return CompletableFuture.completedFuture(text);
        }
        return tryTranslate(text, sourceLang, targetLang, 0);
    }

    private static CompletableFuture<String> tryTranslate(String text, String sourceLang, String targetLang, int attempt) {
        if (attempt >= MAX_RETRIES) {
            System.err.println("Translation failed after " + MAX_RETRIES + " attempts");
            consecutiveFailures++;
            checkFailureThreshold();
            return CompletableFuture.completedFuture(text);
        }

        try {
            String escapedText = text.replace("\"", "\\\"").replace("\n", "\\n");
            String jsonBody = String.format(
                    "{\"q\":\"%s\",\"source\":\"%s\",\"target\":\"%s\"}",
                    escapedText, sourceLang, targetLang
            );

            HttpRequest request = HttpRequest.newBuilder()
                    .uri(URI.create(API_URL))
                    .header("Content-Type", "application/json")
                    .POST(BodyPublishers.ofString(jsonBody))
                    .build();

            return httpClient.sendAsync(request, HttpResponse.BodyHandlers.ofString())
                    .thenApply(response -> {
                        if (response.statusCode() != 200) {
                            System.err.println("API returned status " + response.statusCode());
                            consecutiveFailures++;
                            checkFailureThreshold();
                            return text;
                        }
                        String responseBody = response.body();
                        try {
                            if (!responseBody.contains("\"translatedText\"")) {
                                System.err.println("Invalid API response");
                                consecutiveFailures++;
                                checkFailureThreshold();
                                return text;
                            }
                            consecutiveFailures = 0;
                            return responseBody.split("\"translatedText\":\"")[1].split("\"")[0];
                        } catch (Exception e) {
                            System.err.println("Failed to parse response");
                            consecutiveFailures++;
                            checkFailureThreshold();
                            return text;
                        }
                    })
                    .exceptionally(throwable -> {
                        System.err.println("Translation attempt " + (attempt + 1) + " failed");
                        consecutiveFailures++;
                        checkFailureThreshold();
                        try {
                            Thread.sleep(RETRY_DELAY_MS);
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                        return tryTranslate(text, sourceLang, targetLang, attempt + 1).join();
                    });
        } catch (Exception e) {
            System.err.println("Translation setup failed");
            consecutiveFailures++;
            checkFailureThreshold();
            return CompletableFuture.completedFuture(text);
        }
    }

    private static void checkFailureThreshold() {
        if (consecutiveFailures >= FAILURE_THRESHOLD) {
            apiDisabled = true;
            System.err.println("Disabling API calls due to " + consecutiveFailures + " consecutive failures");
        }
    }
}