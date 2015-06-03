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

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#getPropertyType()
     */
    @Override
    public Class<?> getPropertyType() {
        return boolean.class;
    }

    /* (non-Javadoc)
     * @see greenmirror.fxpropertywrappers.FxPropertyWrapper#getGetMethod(java.lang.Class)
     */
    @Override
    public Method getGetMethod(Class<?> originClass) throws NoSuchMethodException {
        return getGetMethod(originClass, "is");
    }

    
    // -- Commands ---------------------------------------------------------------------------


    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#cast(java.lang.Object)
     */
    @Override
    public Boolean cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return Boolean.valueOf(String.valueOf(instance));
    }

    /* (non-Javadoc)
     * @see greenmirror.fxpropertytype.FxPropertyTypeWrapper#castToMapValue(java.lang.Object)
     */
    @Override
    public Boolean castToMapValue(Object instance) {
        return cast(instance);
    }

}
