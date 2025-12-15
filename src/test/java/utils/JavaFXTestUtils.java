package utils;

import javafx.application.Platform;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

public class JavaFXTestUtils {

    private static boolean initialized = false;

    /** Initialise JavaFX une seule fois */
    public static void initJavaFX() {
        if (!initialized) {
            try {
                CountDownLatch latch = new CountDownLatch(1);
                Platform.startup(latch::countDown);
                latch.await();
                initialized = true;
            } catch (IllegalStateException e) {
                // JavaFX déjà lancé → ignorer
                initialized = true;
            } catch (InterruptedException ignored) {}
        }
    }

    /**
     * Exécute un Runnable sur le thread JavaFX et attend sa fin.
     * POUR LES ACTIONS SANS RETURN
     */
    public static void runAndWait(Runnable action) {
        if (Platform.isFxApplicationThread()) {
            action.run();
            return;
        }

        CountDownLatch latch = new CountDownLatch(1);

        Platform.runLater(() -> {
            try {
                action.run();
            } finally {
                latch.countDown();
            }
        });

        try {
            latch.await();
        } catch (InterruptedException ignored) {}
    }

    /**
     * Exécute un Supplier<T> sur le thread JavaFX et retourne sa valeur.
     * POUR LES ACTIONS AVEC RETURN
     */
    public static <T> T runAndWaitWithResult(SupplierWithException<T> supplier) {
        if (Platform.isFxApplicationThread()) {
            try {
                return supplier.get();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }

        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<T> result = new AtomicReference<>();

        Platform.runLater(() -> {
            try {
                result.set(supplier.get());
            } catch (Exception e) {
                throw new RuntimeException(e);
            } finally {
                latch.countDown();
            }
        });

        try {
            latch.await();
        } catch (InterruptedException ignored) {}

        return result.get();
    }

    @FunctionalInterface
    public interface SupplierWithException<T> {
        T get() throws Exception;
    }
}
