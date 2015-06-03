package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;


/**
 * A wrapper for the <code>String</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class StringFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @see greenmirror.FxPropertyWrapper#FxPropertyTypeWrapper(String)
     * @param propertyName The name of the property.
     */
    public StringFxProperty(String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#getPropertyType()
     */
    @Override
    public Class<?> getPropertyType() {
        return String.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#cast(java.lang.Object)
     */
    @Override
    public String cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return String.valueOf(instance);
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
