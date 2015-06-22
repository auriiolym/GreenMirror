package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;
import org.eclipse.jdt.annotation.NonNull;

import java.lang.reflect.Method;


/**
 * A wrapper for the <code>Boolean</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class BooleanFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param propertyName the name of the property
     * @see greenmirror.FxPropertyWrapper#FxPropertyWrapper(String)
     */
    public BooleanFxProperty(@NonNull String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull 
    public Class<?> getPropertyType() {
        return boolean.class;
    }

    @Override @NonNull 
    public Method getGetMethod(@NonNull Class<?> originClass) throws NoSuchMethodException {
        return getGetMethod(originClass, "is");
    }

    
    // -- Commands ---------------------------------------------------------------------------


    @Override
    public Boolean cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return Boolean.valueOf(String.valueOf(instance));
    }

    @Override
    public Boolean castToMapValue(Object instance) {
        return cast(instance);
    }

}
