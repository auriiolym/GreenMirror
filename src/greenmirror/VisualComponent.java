package greenmirror;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import javafx.animation.Transition;
import javafx.geometry.Point3D;


/**
 * An interface to handle the visual components.
 * 
 * @author Karim El Assal
 */
public interface VisualComponent {
    
    // -- Enumerations -----------------------------------------------------------------------

    public static enum ChangeType {
        NORMAL,
        ADD_NODE,
        REMOVE_NODE,
    }

    // -- Class usage ------------------------------------------------------------------------

    /**
     * Instantiate a <tt>VisualComponent</tt> according to <tt>type</tt>.
     * @param type The class name of the <tt>VisualComponent</tt>.
     * @return     The new <tt>VisualComponent</tt> instance.
     */
    //@ requires type != null;
    public static VisualComponent instantiate(String type) {
        
        try {
            Class<?> vc = Class.forName("greenmirror.visualcomponents." 
                    + Character.toUpperCase(type.charAt(0)) + type.substring(1));
            
            Object instance = vc.newInstance();
            return (instance instanceof VisualComponent) ? (VisualComponent) instance : null;
            
        } catch (ClassNotFoundException | IllegalAccessException
                | InstantiationException | ClassCastException e) {
            return null;
        }
    }
    
    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return A mapping of the properties of this <tt>VisualComponent</tt>.
     */
    //@ ensures \result != null;
    /*@ pure */ public default Map<String, Object> toMap() {
        Map<String, Object> map = new HashMap<>();
        map.put("type", getClass().getSimpleName());
        
        for (Map.Entry<String, Class<?>> property : getChangableProperties().entrySet()) {
            String var = property.getKey();
            Class<?> varType = property.getValue();
            try {
                // Execute getter.
                Object result = getClass().getMethod("get" 
                        + Character.toUpperCase(var.charAt(0)) + var.substring(1)).invoke(this);
                // Cast the result to a double, int or String.
                if (varType.equals(double.class) || varType.equals(Double.class)) {
                    map.put(var, Double.valueOf(String.valueOf(result)));
                } else
                if (varType.equals(int.class) || varType.equals(Integer.class)) {
                    map.put(var, Integer.valueOf(String.valueOf(result)));
                } else {
                    map.put(var, String.valueOf(result));
                }
            } catch (NoSuchMethodException | InvocationTargetException | IllegalAccessException e) {
                e.printStackTrace();;
            }
        }
        return map;
    }
    
    /**
     * @return The GreenMirror <tt>Node</tt> that holds this <tt>VisualComponent</tt>.
     */
    /*@ pure */ public Node getGreenMirrorNode();
    
    /**
     * @return The properties that can be changed by a user of GreenMirror.
     */
    /*@ pure */ public Map<String, Class<?>> getChangableProperties();

    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param node The GreenMirror <tt>Node</tt> that holds this <tt>VisualComponent</tt>.
     */
    //@ ensures getGreenMirrorNode() == node; 
    public void setGreenMirrorNode(Node node);
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Calculate the absolute <tt>Position</tt> of the specified <tt>Placement</tt> on the 
     * <tt>VisualComponent</tt>.
     * @param placement The position of placement which should be calculated.
     * @return          The absolute <tt>Position</tt>.
     */
    public Point3D calculatePosition(Placement placement);

    /**
     * Move the <tt>VisualComponent</tt> to the point where its middle position is equal to
     * <tt>position</tt>.
     * @param position The middle position of the <tt>VisualComponent</tt>.
     */
    //@ requires position != null;
    public void setPositionWithMiddlePoint(Point3D position);

    /**
     * Notify the GreenMirror <tt>Node</tt> that the appearance has been updated.
     */
    public default void appearanceUpdated(Map<String, Object> changedValues) {
        if (getGreenMirrorNode() != null) {
            getGreenMirrorNode().appearanceUpdated(changedValues);
        }
    }
    /**
     * Notify the GreenMirror <tt>Node</tt> that the appearance has been updated.
     */
    public default void appearanceUpdated(Object... propertyPairs) {
        if (getGreenMirrorNode() != null) {
            getGreenMirrorNode().appearanceUpdated(propertyPairs);
        }
    }

    /**
     * @return A deep copy of this <tt>VisualComponent</tt>. 
     */
    //public Object clone();
    
    /**
     * Apply settings from a <tt>Map</tt> of values (from a JSON object, for example).
     * @param map               The <tt>Map</tt> with kay-value pairs.
     * @param changeType        The type of change.
     * @param animationDuration The duration for the animation of the changes.
     * @return                  The <tt>Transition</tt> object that applies the changes.
     */
    //@ requires map != null && changeType != null && animationDuration >= 0;
    //@ ensures \result != null;
    public Transition animateFromMap(Map<String, Object> map, ChangeType changeType, 
                                        double animationDuration);
    
    //@ requires node != null && newValues != null;
    public static void setFromMap(VisualComponent node, Map<String, Object> newValues) {
        
        try {
            // Loop through all to-be-set entries in newValues.
            for (Map.Entry<String, Object> entry : newValues.entrySet()) {
                // Check if it's a valid property.
                if (node.getChangableProperties().containsKey(entry.getKey())) {
                    
                    // Get the variable name and its value.
                    String variable = entry.getKey();
                    String variableC = Character.toUpperCase(variable.charAt(0))
                                            + variable.substring(1);
                    Object value = entry.getValue();
                    
                    // Get the variable type.
                    Class<?> variableType = node.getChangableProperties().get(variable);
                    
                    // Loop through several types.
                    if (variableType.equals(String.class)) {
                        node.getClass().getMethod("set" + variableC, variableType)
                            .invoke(node, String.valueOf(value));
                    } else
                    if (variableType.equals(double.class) || variableType.equals(Double.class)) {
                        node.getClass().getMethod("set" + variableC, variableType)
                            .invoke(node, Double.valueOf(String.valueOf(value)));
                    } else
                    if (variableType.equals(boolean.class) || variableType.equals(Boolean.class)) {
                        node.getClass().getMethod("is" + variableC, variableType)
                            .invoke(node, Boolean.valueOf(String.valueOf(value)));
                    }
                }
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            Log.add("Automatic setting of visual component properties failed: ", e);
        }
    }
}