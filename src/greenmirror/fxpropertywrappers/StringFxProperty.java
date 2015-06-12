package greenmirror.fxpropertywrappers;

import org.eclipse.jdt.annotation.NonNull;

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
    public StringFxProperty(@NonNull String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull 
    public Class<?> getPropertyType() {
        return String.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return String.valueOf(instance);
    }

    @Override
    public String castToMapValue(Object instance) {
        if (instance == null) {
            return null;
        }
        return String.valueOf(instance);
    }

}
