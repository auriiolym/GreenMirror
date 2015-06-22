package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.Log;
import greenmirror.StoredBytesImage;

import org.eclipse.jdt.annotation.NonNull;

import java.io.ByteArrayInputStream;
import java.io.EOFException;
import java.util.Base64;

import javafx.scene.image.Image;

/**
 * A wrapper for the <code>Paint</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class ImageFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param propertyName the name of the property
     * @see greenmirror.FxPropertyWrapper#FxPropertyWrapper(String)
     */
    public ImageFxProperty(@NonNull String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull
    public Class<?> getPropertyType() {
        return Image.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Cast <code>instance</code> to the type represented by this <code>FxPropertyWrapper</code>. 
     * This method only casts <code>Image</code>s, byte arrays and base64 encoded byte arrays 
     * (<code>String</code>s). If anything else is received, it returns <code>null</code>.
     * @param instance The instance of the object. Usually this is received from a (JSON) map.
     * @return         The cast instance; <code>null</code> if <code>instance</code> is null.
     */
    @Override
    public StoredBytesImage cast(Object instance) {
        byte[] bytes = null;
        
        if (instance == null) {
            return null;
        }
        if (instance instanceof StoredBytesImage) {
            return (StoredBytesImage) instance;
        }
        
        // A base64 encoded byte array is assumed if it's a String. 
        if (instance instanceof String) {
            try {
                bytes = Base64.getDecoder().decode(String.valueOf(instance));
            } catch (IllegalArgumentException e) {
                return null;
            }
        }
        if (instance instanceof byte[]) {
            bytes = (byte[]) instance;
        }
        if (bytes != null) {
            final StoredBytesImage image = new StoredBytesImage(new ByteArrayInputStream(bytes));
            image.setBytes(bytes);
            return image;
        }
        
        return null;
    }

    @Override
    public String castToMapValue(Object instance) {
        if (!(instance instanceof StoredBytesImage)) {
            return null;
        }
        final StoredBytesImage image = (StoredBytesImage) instance;
        
        if (image.isError() && image.getException() != null 
                && !(image.getException() instanceof EOFException)) {
            Log.add("The image can't be cast to a map value because of this exception: " 
                    + image.getException().getMessage());
            return null;
        }
        
        final byte[] bytes = image.getBytes();
        
        if (bytes == null) {
            Log.add("The image can't be cast to a map value because there is no byte data "
                    + "stored.");
            return null;
        }
        return Base64.getEncoder().encodeToString(bytes);
    }

}
