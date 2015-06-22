package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;
import org.eclipse.jdt.annotation.NonNull;


/**
 * A wrapper for the <code>String</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class StringFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param propertyName the name of the property
     * @see greenmirror.FxPropertyWrapper#FxPropertyWrapper(String)
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
        return cast(instance);
    }

}
