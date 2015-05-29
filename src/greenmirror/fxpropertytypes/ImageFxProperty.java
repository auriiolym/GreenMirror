package greenmirror.fxpropertytypes;

import java.awt.image.BufferedImage;
import java.awt.image.DataBuffer;
import java.awt.image.DataBufferInt;
import java.io.ByteArrayInputStream;
import java.util.Base64;

import javafx.embed.swing.SwingFXUtils;
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
    public Image cast(Object instance) {
        byte[] bytes = null;
        
        if (instance == null) {
            return null;
        }
        if (instance instanceof Image) {
            return (Image) instance;
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
            return new Image(new ByteArrayInputStream(bytes));
        }
        
        return null;
    }

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#castToMapValue(java.lang.Object)
     */
    @Override
    public String castToMapValue(Object instance) {
        if (!(instance instanceof Image)) {
            return null;
        }
        final Image image = (Image) instance;
        final BufferedImage bufferedImage = SwingFXUtils.fromFXImage(image, null);
        if (bufferedImage == null) {
            return "invalid image";
        }
        
        final DataBuffer dataBuffer = bufferedImage.getData().getDataBuffer();
        int[] ints = null;
        if (dataBuffer instanceof DataBufferInt) {
            ints = ((DataBufferInt) dataBuffer).getData();
        }
        byte[] byt = new byte[ints.length];
        for (int i = 0; i < byt.length; i++) {
            byt[i] = (byte) ints[i];
        }
        //final byte[] bytes = ((DataBufferByte) bufferedImage.getData().getDataBuffer()).getData();
        return Base64.getEncoder().encodeToString(byt);
    }

}
