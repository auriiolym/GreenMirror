package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.IOException;

import javafx.scene.image.Image;

/**
 * An extension of {@link javafx.scene.image.Image} that also saves the bytes of the image itself 
 * in the <code>Image</code> object. This way, it's easier to get a (base64 encoded) string 
 * representation of the image.
 * <p>
 * There is one difficulty here: this object can't simply read the bytes from the 
 * <code>InputStream</code> again to retrieve the bytes. The internal pointer messes that up.
 * Therefore, one should <b>first</b> use {@link #readBytes(InputStream)} to get the bytes, then
 * instantiate the object and finally set them by using {@link #setBytes(byte[])}.
 * 
 * @author Karim El Assal
 */
public class StoredBytesImage extends Image {
    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the individual bytes of the image */
    private byte[] bytes;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * The image can only be retrieved by 
     * 
     * @param inputStream
     */
    public StoredBytesImage(@NonNull InputStream inputStream) {
        super(inputStream);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the individual bytes of the image */
    public byte[] getBytes() {
        return bytes;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /** @param bytes the individual bytes of the image */
    //@ ensures getBytes() == bytes;
    public void setBytes(byte[] bytes) {
        this.bytes = bytes;
    }
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Reads the bytes from the input stream and returns them.
     * 
     * @param inputStream the input stream to read from
     * @return            the read bytes
     * @throws IllegalArgumentException if the input stream could not be read
     */
    @NonNull public static byte[] readBytes(@NonNull InputStream inputStream) {
        try {
            final ByteArrayOutputStream buffer = new ByteArrayOutputStream();
            int read;
            while ((read = inputStream.read()) != -1) {
                buffer.write(read);
            }
            return buffer.toByteArray();
            // Other option: return IOUtils.readFully(inputStream, -1, true);
            // However that option silently leaves an EOFException with the Image object.
        } catch (IOException e) {
            throw new IllegalArgumentException("unable to read image input stream: " 
                    + e.getMessage());
        }
    }
}
