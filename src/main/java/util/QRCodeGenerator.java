package util;

import com.google.zxing.BarcodeFormat;
import com.google.zxing.EncodeHintType;
import com.google.zxing.WriterException;
import com.google.zxing.client.j2se.MatrixToImageWriter;
import com.google.zxing.common.BitMatrix;
import com.google.zxing.qrcode.QRCodeWriter;
import com.google.zxing.qrcode.decoder.ErrorCorrectionLevel;
import javafx.embed.swing.SwingFXUtils;
import javafx.scene.image.Image;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

/**
 * Utility class for generating QR codes
 */
public class QRCodeGenerator {
    
    /**
     * Generate a JavaFX Image QR code from a string
     * 
     * @param text The text to encode in the QR code
     * @param width The width of the QR code
     * @param height The height of the QR code
     * @return JavaFX Image representing the QR code
     * @throws WriterException If there is an error generating the QR code
     * @throws IOException If there is an error converting the QR code to an image
     */
    public static Image generateQRCodeImage(String text, int width, int height) throws WriterException, IOException {

        Map<EncodeHintType, Object> hints = new HashMap<>();
        hints.put(EncodeHintType.ERROR_CORRECTION, ErrorCorrectionLevel.H);
        

        QRCodeWriter qrCodeWriter = new QRCodeWriter();
        BitMatrix bitMatrix = qrCodeWriter.encode(text, BarcodeFormat.QR_CODE, width, height, hints);
        

        BufferedImage bufferedImage = MatrixToImageWriter.toBufferedImage(bitMatrix);
        

        return SwingFXUtils.toFXImage(bufferedImage, null);
    }
    
    /**
     * Generate a QR code and return it as a byte array
     * 
     * @param text The text to encode in the QR code
     * @param width The width of the QR code
     * @param height The height of the QR code
     * @return Byte array representing the QR code image
     * @throws WriterException If there is an error generating the QR code
     * @throws IOException If there is an error converting the QR code to an image
     */
    public static byte[] generateQRCodeBytes(String text, int width, int height) throws WriterException, IOException {

        Map<EncodeHintType, Object> hints = new HashMap<>();
        hints.put(EncodeHintType.ERROR_CORRECTION, ErrorCorrectionLevel.H);
        hints.put(EncodeHintType.MARGIN, 2);
        

        QRCodeWriter qrCodeWriter = new QRCodeWriter();
        BitMatrix bitMatrix = qrCodeWriter.encode(text, BarcodeFormat.QR_CODE, width, height, hints);
        

        BufferedImage bufferedImage = MatrixToImageWriter.toBufferedImage(bitMatrix);
        

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        ImageIO.write(bufferedImage, "png", baos);
        return baos.toByteArray();
    }
} 