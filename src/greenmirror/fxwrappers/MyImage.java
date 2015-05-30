package greenmirror.fxwrappers;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;

import javafx.scene.image.Image;

/**
 * 
 * @author Karim El Assal
 */
public class MyImage extends Image {
    
    
    /**
     * @param inputStream
     */
    public MyImage(InputStream inputStream) {
        super(inputStream);
    }
    
    
    private byte[] bytes;
    
    public byte[] getBytes() {
        return bytes;
    }
    
    public void setBytes(byte[] bytes) {
        this.bytes = bytes;
    }

    
    public static byte[] readBytes(InputStream inputStream) {
        try {
            final ByteArrayOutputStream buffer = new ByteArrayOutputStream();
            int read;
            while ((read = inputStream.read()) != -1) {
                buffer.write(read);
            }
            return buffer.toByteArray();
            // Other option: return IOUtils.readFully(inputStream, -1, true);
        } catch (IOException e) {
            throw new IllegalArgumentException("Unable to read image input stream: " 
                    + e.getMessage());
        }
    }
}
