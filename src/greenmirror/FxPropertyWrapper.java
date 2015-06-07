package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.lang.reflect.Method;
import java.util.List;

import javafx.util.Duration;

/**
 * A wrapper class for handling JavaFX properties.
 * <p>
 * It provides several methods to make adding properties to an {@link FxWrapper} as easy as 
 * possible.
 * 
 * @author Karim El Assal
 */
public abstract class FxPropertyWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the name of the property */
    private String propertyName;
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Creates a new <code>FxPropertyWrapper</code> with <code>propertyName</code>.
     * 
     * @param propertyName          the name of the property this <code>FxPropertyWrapper</code> 
     *                              is representing with the correct case (first character lower
     *                              case, the rest as its get or set methods)
     */
    //@ ensures getPropertyName() == propertyName;
    public FxPropertyWrapper(@NonNull String propertyName) {
        setPropertyName(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the property name */
    /*@ pure */ @NonNull public String getPropertyName() {
        return propertyName == null ? "" : propertyName + "";
    }
    
    /**
     * Returns the property type, which should be equal to the setter type when this property
     * is set at an FX node. For example: if an <code>FxPropertyWrapper</code> subclass is 
     * created for wrapping <code>double</code> properties of any JavaFX node, this method should 
     * return <code>double.class</code>. The JavaFX node could have a method 
     * <code>setRotate(double)</code>, so the subclass is a perfect wrapper for the 
     * <code>rotate</code> property.
     * 
     * @return the property type
     */
    /*@ pure */ @NonNull public abstract Class<?> getPropertyType();
    
    /**
     * Gets the set method of <code>originClass</code> for this <code>FxPropertyWrapper</code>.
     * 
     * @param originClass the origin class that has the returned method
     * @return            the <code>Method</code> that can be invoked with an argument of the same 
     *                    type as this <code>FxPropertyWrapper</code> was created for (retrieved
     *                    by calling {@link #getPropertyType()}), with the signature:
     *                    <code>setPropertyName(PropertyType)</code>
     * @throws NoSuchMethodException if the method was not found
     */
    /*@ pure */ @NonNull public Method getSetMethod(@NonNull Class<?> originClass) 
            throws NoSuchMethodException {
        final Method method = originClass.getMethod("set" 
                            + GreenMirrorUtils.capitalizeFirstChar(getPropertyName()), 
                            getPropertyType());
        if (method == null) {
            throw new NoSuchMethodException("setter for " + getPropertyName());
        }
        return method;
    }
    
    /**
     * Gets the get method of <code>originClass</code> for this <code>FxPropertyWrapper</code>.
     * 
     * @param originClass the origin class that has the returned method
     * @return            the <code>Method</code> that returns an object of the same 
     *                    type as this <code>FxPropertyWrapper</code> was created for (retrieved
     *                    by calling {@link #getPropertyType()}), with the signature:
     *                    <code>getPropertyName()</code>
     * @throws NoSuchMethodException if the method was not found.
     */
    /*@ pure */ @NonNull public Method getGetMethod(@NonNull Class<?> originClass) 
            throws NoSuchMethodException {
        return getGetMethod(originClass, "get");
    }
    
    /**
     * Gets the get method of <code>originClass</code> for this <code>FxPropertyWrapper</code>
     * with prefix <code>methodNamePrefix</code>.
     * 
     * @param originClass      the origin class that has the returned method
     * @param methodNamePrefix the prefix of the method name. Usually this is "get"
     * @return                 the <code>Method</code> that returns an object of the same 
     *                         type as this <code>FxPropertyWrapper</code> was created for
     *                         (retrieved by calling {@link #getPropertyType()}), with the
     *                         signature: <code>methodNamePrefixPropertyName()</code>
     * @throws NoSuchMethodException if the method was not found
     */
    /*@ pure */ @NonNull public Method getGetMethod(@NonNull Class<?> originClass, 
            @NonNull String methodNamePrefix) throws NoSuchMethodException {
        final Method method = originClass.getMethod(methodNamePrefix 
                        + GreenMirrorUtils.capitalizeFirstChar(getPropertyName()));
        if (method == null) {
            throw new NoSuchMethodException("prefix: " + methodNamePrefix + ", property: " 
                    + getPropertyName());
        }
        return method;
    }
    
    /**
     * Gets the animate method of <code>originClass</code> for this <code>FxPropertyWrapper</code>.
     * 
     * @param originClass the origin class that has the returned method
     * @return            the <code>Method</code> that creates an animation of the changing value 
     *                    of the same type as this <code>FxPropertyWrapper</code> was created for
     *                    (retrieved by calling {@link #getPropertyType()}), with the signature:
     *                    <code>animatePropertyName(PropertyType, Duration)</code>
     * @throws NoSuchMethodException if the method was not found
     */
    /*@ pure */ @NonNull public Method getAnimateMethod(@NonNull Class<?> originClass) 
            throws NoSuchMethodException {
        final Method method = originClass.getMethod("animate" 
                        + GreenMirrorUtils.capitalizeFirstChar(getPropertyName()),
                        getPropertyType(), Duration.class);
        if (method == null) {
            throw new NoSuchMethodException("animator for " + getPropertyName());
        }
        return method;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param propertyName the property name to set
     */
    //@ ensures getPropertyName() == propertyName;
    protected void setPropertyName(@NonNull String propertyName) {
        this.propertyName = propertyName;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Casts <code>instance</code> to the type represented by this <code>FxPropertyWrapper</code>.
     * The cast, returned value should have no trouble being passed to the set method of this
     * <code>FxPropertyWrapper</code>. For example, when a set method accepts <code>double</code>
     * values, this method can return a <code>Double</code> type. The overriding method should
     * have a return type more specific than the current <code>Object</code>.
     * 
     * @param instance the instance of the property. Usually this is received from a (JSON) map
     * @return         the cast instance; <code>null</code> if <code>instance</code> is null or
     *                 the instance could not be cast
     */
    //@ ensures \result == (instance == null ? null : \result);
    public abstract Object cast(Object instance);
    
    /**
     * Casts <code>instance</code> to a type that can be represented by "stringifiable" map, such as
     * a JSON map.
     * 
     * @param instance the instance of the object
     * @return         the cast instance. Usually this is a <code>String</code>, an 
     *                 <code>Integer</code> or a <code>Double</code>. Returns <code>null</code> 
     *                 if <code>instance</code> is <code>null</code>.
     */
    //@ ensures \result == (instance == null ? null : \result);
    public abstract Object castToMapValue(Object instance);
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Checks if a <code>List</code> of <code>FxPropertyWrapper</code>s has an
     * <code>FxPropertyWrapper</code> with the specific property <code>name</code>.
     * 
     * @param list the <code>List</code> to search through
     * @param name the property name to search for
     * @return     <code>true</code> if it was found
     */
    /*@ pure */ public static boolean hasPropertyName(
            @NonNull List<FxPropertyWrapper> list, @NonNull String name) {
        return getFromList(list, name) != null;
    }
    
    /**
     * Returns the <code>FxPropertyWrapper</code> from <code>list</code> that has the property
     * name <code>name</code> or <code>null</code> if it wasn't found.
     * 
     * @param list the <code>List</code> to search through
     * @param name the property name to search for
     * @return     the <code>FxPropertyWrapper</code>; <code>null</code> if it wasn't found
     */
    /*@ pure */ public static FxPropertyWrapper getFromList(
            @NonNull List<FxPropertyWrapper> list, String name) {
        for (FxPropertyWrapper fxProperty : list) {
            if (fxProperty.getPropertyName().equals(name)) {
                return fxProperty;
            }
        }
        return null;
    }

}
