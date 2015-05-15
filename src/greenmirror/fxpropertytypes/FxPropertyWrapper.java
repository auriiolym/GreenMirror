package greenmirror.fxpropertytypes;

import java.lang.reflect.Method;
import java.util.List;

import javafx.util.Duration;

/**
 * A class that holds shared code for several FxContainerProperty types.
 * 
 * @author Karim El Assal
 */
public abstract class FxPropertyWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    //@ private invariant propertyName != null;
    private String propertyName;
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>FxPropertyWrapper</tt> with <tt>propertyName</tt>.
     * @param propertyName The name of the property this <tt>FxPropertyWrapper</tt> is
     *                     representing. <tt>propertyName</tt> can't be <tt>null</tt>.
     */
    //@ requires propertyName != null;
    //@ ensures getPropertyName() == propertyName;
    public FxPropertyWrapper(String propertyName) {
        setPropertyName(propertyName);
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The property name. It has to be in the correct capitalization, without a capital
     *         as its first character.
     */
    //@ ensures \result != null;
    /*@ pure */ public String getPropertyName() {
        return propertyName;
    }
    
    /**
     * @return The property type.
     */
    /*@ pure */ public abstract Class<?> getPropertyType();
    
    /**
     * Get the set method of <tt>originClass</tt> for this <tt>FxPropertyWrapper</tt>.
     * @param originClass The origin class.
     * @return            The <tt>Method</tt> that can be invoked with an argument of the same 
     *                    type as this <tt>FxPropertyWrapper</tt> was created for.
     * @throws NoSuchMethodException If the method was not found.
     */
    //@ requires originClass != null;
    /*@ pure */ public Method getSetMethod(Class<?> originClass) throws NoSuchMethodException {
        return originClass.getMethod("set" + capitalizeFirstChar(getPropertyName()), 
                                     getPropertyType());
    }
    
    /**
     * Get the get method of <tt>originClass</tt> for this <tt>FxPropertyWrapper</tt>.
     * @param originClass The origin class.
     * @return            The <tt>Method</tt> that returns an object of the same 
     *                    type as this <tt>FxPropertyWrapper</tt> was created for.
     * @throws NoSuchMethodException If the method was not found.
     */
    //@ requires originClass != null;
    /*@ pure */ public Method getGetMethod(Class<?> originClass) throws NoSuchMethodException {
        return getGetMethod(originClass, "get");
    }
    
    /**
     * Get the get method of <tt>originClass</tt> for this <tt>FxPropertyWrapper</tt>.
     * @param originClass      The origin class.
     * @param methodNamePrefix The prefix of the method name. Usually this is "get".
     * @return                 The <tt>Method</tt> that returns an object of the same 
     *                         type as this <tt>FxPropertyWrapper</tt> was created for.
     * @throws NoSuchMethodException If the method was not found.
     */
    //@ requires originClass != null && methodNamePrefix != null;
    /*@ pure */ public Method getGetMethod(Class<?> originClass, String methodNamePrefix) 
            throws NoSuchMethodException {
        return originClass.getMethod(methodNamePrefix + capitalizeFirstChar(getPropertyName()));
    }
    
    /**
     * Get the animate method of <tt>originClass</tt> for this <tt>FxPropertyWrapper</tt>.
     * @param originClass The origin class.
     * @return            The <tt>Method</tt> that creates an animation of the changing value 
     *                    of the same type as this <tt>FxPropertyWrapper</tt> was created for.
     * @throws NoSuchMethodException If the method was not found.
     */
    //@ requires originClass != null;
    /*@ pure */ public Method getAnimateMethod(Class<?> originClass) throws NoSuchMethodException {
        return originClass.getMethod("animate" + capitalizeFirstChar(getPropertyName()),
                                     getPropertyType(),
                                     Duration.class);
    }
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param propertyName The property name to set.
     */
    //@ requires propertyName != null;
    //@ ensures getPropertyName() == propertyName;
    protected void setPropertyName(String propertyName) {
        this.propertyName = propertyName;
    }
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Capitalize the first character of a <tt>String</tt>.
     * @param str The <tt>String</tt>.
     * @return    The <tt>String</tt> with its first character capitalized.
     */
    //@ requires str != null;
    //@ ensures \result != null;
    //@ ensures \result.equals(Character.toUpperCase(str.charAt(0)) + str.substring(1));
    /*@ pure */ public static String capitalizeFirstChar(String str) {
        return Character.toUpperCase(str.charAt(0)) + str.substring(1);
    }
    
    /**
     * Check if a <tt>List</tt> of <tt>FxPropertyWrapper</tt>s has a specific property name.
     * @param list The <tt>List</tt> to search through.
     * @param name The property name to search for.
     * @return     <tt>true</tt> if it was found.
     */
    //@ requires list != null && name != null;
    /*@ pure */ public static boolean hasPropertyName(List<FxPropertyWrapper> list, String name) {
        for (FxPropertyWrapper fxProperty : list) {
            if (name.equals(fxProperty.getPropertyName())) {
                return true;
            }
        }
        //TODO: make this a lambda function (?)
        return false;
    }
    
    /*@ pure */ public static FxPropertyWrapper getFromList(List<FxPropertyWrapper> list, 
                                                            String name) {
        for (FxPropertyWrapper fxProperty : list) {
            if (name.equals(fxProperty.getPropertyName())) {
                return fxProperty;
            }
        }
        //TODO: make this a lambda function (?)
        return null;
    }
    
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Cast <tt>instance</tt> to the type represented by this <tt>FxPropertyWrapper</tt>.
     * @param instance The instance of the object. Usually this is received from a (JSON) map.
     * @return         The cast instance; <tt>null</tt> if <tt>instance</tt> is null.
     */
    public abstract Object cast(Object instance);
    
    /**
     * Cast <tt>instance</tt> to a type that can be represented by "stringifiable" map, such as
     * a JSON map.
     * @param instance The instance of the object.
     * @return         The cast instance. Usually this is a <tt>String</tt>, an <tt>Integer</tt>
     *                 or a <tt>Double</tt>. Returns <tt>null</tt> if <tt>instance</tt> is null.
     */
    public abstract Object castToMapValue(Object instance);

}
