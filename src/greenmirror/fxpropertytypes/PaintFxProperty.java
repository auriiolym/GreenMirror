package greenmirror.fxpropertytypes;

import javafx.scene.paint.Paint;

/**
 * A wrapper for the <tt>Paint</tt> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class PaintFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @see greenmirror.fxpropertytypes.FxPropertyWrapper#FxPropertyTypeWrapper(String)
     * @param propertyName The name of the property.
     */
    public PaintFxProperty(String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#getPropertyType()
     */
    @Override
    public Class<?> getPropertyType() {
        return Paint.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#cast(java.lang.Object)
     */
    @Override
    public Paint cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return Paint.valueOf(String.valueOf(instance));
    }

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#castToMapValue(java.lang.Object)
     */
    @Override
    public String castToMapValue(Object instance) {
        if (instance == null) {
            return null;
        }
        return String.valueOf(instance);
    }

}
