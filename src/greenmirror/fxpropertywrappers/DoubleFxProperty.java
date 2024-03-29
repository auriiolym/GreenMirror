package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;

import org.eclipse.jdt.annotation.NonNull;

/**
 * A wrapper for the <code>Double</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class DoubleFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param propertyName the name of the property
     * @see greenmirror.FxPropertyWrapper#FxPropertyWrapper(String)
     */
    public DoubleFxProperty(@NonNull String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull
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
