package greenmirror.fxpropertytypes;

import greenmirror.Log;
import greenmirror.fxwrappers.MyImage;

import java.io.ByteArrayInputStream;
import java.io.EOFException;
import java.util.Base64;

import javafx.scene.image.Image;

/**
 * A wrapper for the <tt>Paint</tt> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class ImageFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @see greenmirror.fxpropertytypes.FxPropertyWrapper#FxPropertyTypeWrapper(String)
     * @param propertyName The name of the property.
     */
    public ImageFxProperty(String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#getPropertyType()
     */
    @Override
    public Class<?> getPropertyType() {
        return Image.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Cast <tt>instance</tt> to the type represented by this <tt>FxPropertyWrapper</tt>. This
     * method only casts <tt>Image</tt>s, byte arrays and base64 encoded byte arrays 
     * (<tt>String</tt>s). If anything else is received, it returns <tt>null</tt>.
     * @param instance The instance of the object. Usually this is received from a (JSON) map.
     * @return         The cast instance; <tt>null</tt> if <tt>instance</tt> is null.
     */
    @Override
    public MyImage cast(Object instance) {
        byte[] bytes = null;
        
        if (instance == null) {
            return null;
        }
        if (instance instanceof MyImage) {
            return (MyImage) instance;
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
            final MyImage image = new MyImage(new ByteArrayInputStream(bytes));
            image.setBytes(bytes);
            return image;
        }
        
        return null;
    }

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#castToMapValue(java.lang.Object)
     */
    @Override
    public String castToMapValue(Object instance) {
        if (!(instance instanceof MyImage)) {
            return null;
        }
        final MyImage image = (MyImage) instance;
        
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
