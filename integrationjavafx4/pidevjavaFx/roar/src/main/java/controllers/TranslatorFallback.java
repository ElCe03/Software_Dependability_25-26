package controllers;

import java.util.HashMap;
import java.util.Map;

public class TranslatorFallback {

    //@ public invariant translations != null;
    //@ public invariant (\forall String lang; translations.containsKey(lang) ==> translations.get(lang) != null);
    //@ public invariant (\forall String lang; translations.containsKey(lang) ==> 
    //@                      (\forall String k; translations.get(lang).containsKey(k) ==> 
    //@                           translations.get(lang).get(k) != null));

    private static final Map<String, Map<String, String>> translations = new HashMap<>();

    static {
        // English to French
        Map<String, String> enToFr = new HashMap<>();
        enToFr.put("Service Details - %s", "Détails du service - %s");
        enToFr.put("Close", "Fermer");
        enToFr.put("Duration:", "Durée :");
        enToFr.put("%d minutes", "%d minutes");
        enToFr.put("Description:", "Description :");
        enToFr.put("See Service Details", "Voir les détails du service");
        enToFr.put("⏱ %d minutes", "⏱ %d minutes");
        enToFr.put("Navigation Error", "Erreur de navigation");
        enToFr.put("Failed to load the front page.", "Échec du chargement de la page d'accueil.");
        enToFr.put("Translation unavailable, using English.", "Traduction indisponible, utilisation de l'anglais.");
        enToFr.put("Loading Error", "Erreur de chargement");
        enToFr.put("Failed to load services in time.", "Échec du chargement des services.");
        translations.put("fr", enToFr);

        // English to Spanish
        Map<String, String> enToEs = new HashMap<>();
        enToEs.put("Service Details - %s", "Detalles del servicio - %s");
        enToEs.put("Close", "Cerrar");
        enToEs.put("Duration:", "Duración:");
        enToEs.put("%d minutes", "%d minutos");
        enToEs.put("Description:", "Descripción:");
        enToEs.put("See Service Details", "Ver detalles del servicio");
        enToEs.put("⏱ %d minutes", "⏱ %d minutos");
        enToEs.put("Navigation Error", "Error de navegación");
        enToEs.put("Failed to load the front page.", "No se pudo cargar la página principal.");
        enToEs.put("Translation unavailable, using English.", "Traducción no disponible, usando inglés.");
        enToEs.put("Loading Error", "Error de carga");
        enToEs.put("Failed to load services in time.", "No se pudieron cargar los servicios a tiempo.");
        translations.put("es", enToEs);

        // English to German
        Map<String, String> enToDe = new HashMap<>();
        enToDe.put("Service Details - %s", "Dienstleistungsdetails - %s");
        enToDe.put("Close", "Schließen");
        enToDe.put("Duration:", "Dauer:");
        enToDe.put("%d minutes", "%d Minuten");
        enToDe.put("Description:", "Beschreibung:");
        enToDe.put("See Service Details", "Dienstleistungsdetails anzeigen");
        enToDe.put("⏱ %d minutes", "⏱ %d Minuten");
        enToDe.put("Navigation Error", "Navigationsfehler");
        enToDe.put("Failed to load the front page.", "Die Startseite konnte nicht geladen werden.");
        enToDe.put("Translation unavailable, using English.", "Übersetzung nicht verfügbar, Englisch wird verwendet.");
        enToDe.put("Loading Error", "Ladefehler");
        enToDe.put("Failed to load services in time.", "Dienste konnten nicht rechtzeitig geladen werden.");
        translations.put("de", enToDe);

        // English to Arabic
        Map<String, String> enToAr = new HashMap<>();
        enToAr.put("Service Details - %s", "تفاصيل الخدمة - %s");
        enToAr.put("Close", "إغلاق");
        enToAr.put("Duration:", "المدة:");
        enToAr.put("%d minutes", "%d دقيقة");
        enToAr.put("Description:", "الوصف:");
        enToAr.put("See Service Details", "عرض تفاصيل الخدمة");
        enToAr.put("⏱ %d minutes", "⏱ %d دقيقة");
        enToAr.put("Navigation Error", "خطأ في التنقل");
        enToAr.put("Failed to load the front page.", "فشل تحميل الصفحة الرئيسية.");
        enToAr.put("Translation unavailable, using English.", "الترجمة غير متوفرة، يتم استخدام الإنجليزية.");
        enToAr.put("Loading Error", "خطأ في التحميل");
        enToAr.put("Failed to load services in time.", "فشل تحميل الخدمات في الوقت المحدد.");
        translations.put("ar", enToAr);
    }

     /*@ public normal_behavior
      @   requires text != null ==> true;     // text may be null
      @   requires targetLang != null ==> true;   // targetLang may be null
      @   assignable \nothing;
      @   ensures (text == null) ==> \result == null;
      @   ensures (targetLang == null) ==> \result == text;
      @   ensures (targetLang != null && targetLang.equals("en")) ==> \result == text;
      @   ensures translations.containsKey(targetLang) ==> 
      @            (translations.get(targetLang).containsKey(text) ==> 
      @                 \result.equals(translations.get(targetLang).get(text)));
      @   ensures !translations.containsKey(targetLang) ==> \result == text;
      @ also
      @ public exceptional_behavior
      @   assignable \nothing;
      @*/

    public static String translate(String text, String targetLang) {
        if (text == null || targetLang == null || targetLang.equals("en")) {
            return text;
        }

        Map<String, String> langTranslations = translations.get(targetLang);
        if (langTranslations != null) {
            // Check for exact matches first
            if (langTranslations.containsKey(text)) {
                return langTranslations.get(text);
            }

            // Check for formatted strings
            for (Map.Entry<String, String> entry : langTranslations.entrySet()) {
                if (text.startsWith(entry.getKey().split("%")[0])) {
                    try {
                        return String.format(entry.getValue(), text.split("%")[1].split(" ")[0]);
                    } catch (Exception e) {
                        return text;
                    }
                }
            }
        }
        return text;
    }
}