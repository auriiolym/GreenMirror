package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;

import java.lang.reflect.Method;


/**
 * A wrapper for the <code>Paint</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class BooleanFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @see greenmirror.FxPropertyWrapper#FxPropertyTypeWrapper(String)
     * @param propertyName The name of the property.
     */
    public BooleanFxProperty(String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override
    public Class<?> getPropertyType() {
        return boolean.class;
    }

    @Override
    public Method getGetMethod(Class<?> originClass) throws NoSuchMethodException {
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
