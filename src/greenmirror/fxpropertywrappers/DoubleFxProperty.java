package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;

/**
 * A wrapper for the <code>Double</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class DoubleFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @see greenmirror.FxPropertyWrapper#FxPropertyTypeWrapper(String)
     * @param propertyName The name of the property.
     */
    public DoubleFxProperty(String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override
    public Class<?> getPropertyType() {
        return double.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public Double cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return Double.valueOf(String.valueOf(instance));
    }

    @Override
    public Double castToMapValue(Object instance) {
        return cast(instance);
    }

}
