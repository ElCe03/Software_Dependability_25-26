package utils;

import javafx.application.Platform;

import java.util.concurrent.CountDownLatch;

public class FxTestInitializer {

    private static boolean started = false;

    public static void init() {
        if (!started) {
            started = true;
            CountDownLatch latch = new CountDownLatch(1);
            Platform.startup(latch::countDown);
            try {
                latch.await();
            } catch (InterruptedException ignored) {}
        }
    }

    public static void runOnFxThread(Runnable task) {
        if (Platform.isFxApplicationThread()) {
            task.run();
        } else {
            CountDownLatch latch = new CountDownLatch(1);
            Platform.runLater(() -> {
                try { task.run(); }
                finally { latch.countDown(); }
            });
            try { latch.await(); }
            catch (InterruptedException ignored) {}
        }
    }
}
