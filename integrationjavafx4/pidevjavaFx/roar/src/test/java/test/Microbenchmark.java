package test;

import org.openjdk.jmh.annotations.*;
import util.QRCodeGenerator;
import org.mindrot.jbcrypt.BCrypt;
import java.util.concurrent.TimeUnit;
import java.io.IOException;
import com.google.zxing.WriterException;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(value = 0, warmups = 0)
@Warmup(iterations = 3) 
@Measurement(iterations = 5)  
public class Microbenchmark {

    // Parametri per il test del QR Code
    @Param({"100", "500", "1000"})
    public int qrSize;

    private String qrText = "SoftwareDependabilityProject2025";
    
    @Param({"10", "12"}) 
    public int logRounds;
    
    private String password = "MySuperSecretPassword123!";

    @Benchmark
    public void testQRCodeGeneration() throws WriterException, IOException {
        QRCodeGenerator.generateQRCodeBytes(qrText, qrSize, qrSize);
    }

    @Benchmark
    public void testBCryptHashing() {
        BCrypt.hashpw(password, BCrypt.gensalt(logRounds));
    }

    public static void main(String[] args) throws Exception {
        org.openjdk.jmh.runner.Runner runner = new org.openjdk.jmh.runner.Runner(
                new org.openjdk.jmh.runner.options.OptionsBuilder()
                        .include(Microbenchmark.class.getSimpleName())
                        .build()
        );
        runner.run();
    }
}