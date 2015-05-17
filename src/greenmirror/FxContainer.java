package greenmirror;

import greenmirror.fxcontainers.RectangleFxContainer;
import greenmirror.fxpropertytypes.DoubleFxProperty;
import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.fxpropertytypes.StringFxProperty;
import groovy.json.JsonOutput;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;

import javafx.animation.FadeTransition;
import javafx.animation.ParallelTransition;
import javafx.animation.RotateTransition;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Point3D;
import javafx.scene.paint.Color;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public abstract class FxContainer extends Observable {
    
    // -- Enumerations -----------------------------------------------------------------------

    // -- Exceptions -------------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    private FxContainer originalFx;
    
    private javafx.scene.Node fxNode;
    
    private double rotate;
    private double opacity = 1.0;
    private String style;

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
 
    /**
     * @return The type of the FxContainer.
     */
    /*@ pure */ public String getType() {
        return getClass().getSimpleName().replace("FxContainer", "");
    }
    
    /*@ pure */ public javafx.scene.Node getFxNode() {
        return this.fxNode;
    }
    
    /*@ pure */ public double getRotate() {
        return this.rotate;
    }
    
    /*@ pure */ public double getOpacity() {
        return this.opacity;
    }
    
    /*@ pure */ public String getStyle() {
        return this.style;
    }

    /**
     * @return A mapping of the properties of this <tt>VisualComponent</tt>.
     */
    //@ ensures \result != null;
    /*@ pure */ public Map<String, Object> toMap() {
        Map<String, Object> map = new HashMap<>();
        map.put("type", getType());
        
        for (FxPropertyWrapper fxProperty : getChangableProperties()) {
            String var = fxProperty.getPropertyName();
            
            try {
                // Execute getter.
                Object result = fxProperty.getGetMethod(this.getClass()).invoke(this);
                
                // Put result into map.
                map.put(var, fxProperty.castToMapValue(result));
                
            } catch (NoSuchMethodException | InvocationTargetException | IllegalAccessException e) {
                //TODO: make this throw a RuntimeException.
                e.printStackTrace();
            }
        }
        return map;
    }
    
    // test DoubleFxProperty
    public static void main(String[] args) {
        RectangleFxContainer rect = new RectangleFxContainer();
        rect.setX(4);
        rect.setY(1);
        rect.setWidth(2);
        rect.setHeight(3);
        rect.setFill(Color.RED);
        Map<String, Object> map = rect.toMap();
        System.out.println(JsonOutput.prettyPrint(JsonOutput.toJson(map)));
        
        RectangleFxContainer rect2 = new RectangleFxContainer();
        rect2.setFromMap(map);
        Map<String, Object> map2 = rect2.toMap();
        System.out.println(JsonOutput.prettyPrint(JsonOutput.toJson(map2)));
    }
    
    /**
     * @return The properties that can be changed and animated by a user of GreenMirror.
     */
    /*@ pure */ protected List<FxPropertyWrapper> getAnimatableProperties() {
        return new ArrayList<FxPropertyWrapper>() {
            {
                add(new DoubleFxProperty("rotate"));
                add(new DoubleFxProperty("opacity"));
            }
        };
    }
    
    /**
     * @return The properties that can be changed by a user of GreenMirror (but cannot be 
     *         animated, meaning that they can only be set once).
     */
    //TODO: check if the above description holds.
    /*@ pure */ protected List<FxPropertyWrapper> getChangableProperties() {
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(getAnimatableProperties());
                add(new StringFxProperty("style"));
            }
        };
    }
    
    /**
     * @return A String representation of this FxContainer.
     */
    @Override
    /*@ pure */ public String toString() {
        String str = getClass().getSimpleName() + toMap().toString();
        return str;
    }
    
    /**
     * Check if the position of the FX node was set. Usually it just checks if the x and y values 
     * are set.
     * @return <tt>true</tt> if the position was set.
     */
    /*@ pure */ public abstract boolean isPositionSet();
    
    /**
     * Calculate the absolute position of the specified <tt>Placement</tt> on the 
     * <tt>VisualComponent</tt>.
     * @param placement The position of placement which should be calculated.
     * @return          The absolute <tt>Position</tt>.
     */
    //@ requires placement != null;
    //@ ensures \result != null;
    public abstract Point3D calculatePoint(Placement placement);
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    protected void setFxNode(javafx.scene.Node node) {
        this.fxNode = node;
    }
    
    public FxContainer setRotate(double value) {
        this.rotate = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxContainer setOpacity(double value) {
        this.opacity = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxContainer setStyle(String value) {
        this.style = value;
        setChanged();
        notifyObservers();
        return this;
    }

    //@ requires newValues != null;
    public void setFromMap(Map<String, Object> newValues) {
        String property = null;
        Object value = null;
        try {
            // Loop through all to-be-set entries in newValues.
            for (Map.Entry<String, Object> entry : newValues.entrySet()) {
                
                // Get property name and value.
                property = entry.getKey();
                value = entry.getValue();
                FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
                        getChangableProperties(), property);
                
                // Continue to the next if there is no FxPropertyWrapper or if the value is null.
                if (fxPropertyWrapper == null || value == null) {
                    continue;
                }
                
                // Get set method and execute with the cast value.
                fxPropertyWrapper.getSetMethod(this.getClass())
                                 .invoke(this, fxPropertyWrapper.cast(value));
                
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            Log.add("Automatic setting of FX container property (" + property + ") failed: ", e);
        }
    }
    
    /**
     * Set the properties of the JavaFX node from a <tt>Map</tt>.
     * @param newValues The variable-value-map with new values.
     */
    //@ requires newValues != null;
    public void setFxNodeValuesFromMap(Map<String, Object> newValues) {
        String property = null;
        Object value = null;
        try {
            // Loop through all to-be-set entries in newValues.
            for (Map.Entry<String, Object> entry : newValues.entrySet()) {
                

                // Get property name and value.
                property = entry.getKey();
                value = entry.getValue();
                FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
                        getChangableProperties(), property);
                
                // Continue to the next if there is no FxPropertyWrapper or if the value is null.
                if (fxPropertyWrapper == null || value == null) {
                    continue;
                }
                
                // Get set method and execute with the cast value.
                fxPropertyWrapper.getSetMethod(getFxNode().getClass())
                                 .invoke(getFxNode(), fxPropertyWrapper.cast(value));
                
            }
        } catch (IllegalAccessException | NoSuchMethodException e) {
            Log.add("Automatic setting of JavaFX node property (" + property + ":" 
                    + String.valueOf(value) + ") failed: ", e);
        } catch (InvocationTargetException e) {
            Log.add("Automatic setting of JavaFX node property (" + property + ") gave its "
                    + "own exception: ", e.getCause());
        }
    }
    
    public Transition animateRotate(double value, Duration duration) {
        RotateTransition transition = new RotateTransition(duration, getFxNode());
        transition.setToAngle(value);
        return transition;
    }
    
    public Transition animateOpacity(double value, Duration duration) {
        FadeTransition transition = new FadeTransition(duration, getFxNode());
        transition.setToValue(value);
        return transition;
    }
    
    public Transition animateAppearing(Duration duration) {
        FadeTransition transition = (FadeTransition) animateOpacity(getOpacity(), duration);
        transition.setFromValue(0);
        transition.setOnFinished(new EventHandler<ActionEvent>() {
            @Override
            public void handle(ActionEvent event) {
                transition.getNode().setMouseTransparent(false);
            }
        });
        return transition;
    }
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Instantiate a new <tt>FxContainer</tt>.
     * @param type The type, which should be the same as the class name in the 
     *             <tt>greenmirror.fxcontainers</tt> package, appended with <tt>FxContainer</tt>.
     *             The first letter will be capitalized.
     * @return     The new instance.
     * @throws IllegalArgumentException If the passed type is invalid.
     */
    //@ requires type != null;
    public static FxContainer instantiate(String type) {
        try {
            Class<?> vc = Class.forName("greenmirror.fxcontainers." 
                    + Character.toUpperCase(type.charAt(0)) + type.substring(1) + "FxContainer");

            return (FxContainer) vc.newInstance();
            
        } catch (ClassNotFoundException | IllegalAccessException
                | InstantiationException | ClassCastException e) {
            // Throw Exception if it wasn't possible to create the FxContainer.
            throw new IllegalArgumentException("The passed FX type (" + type + ") is invalid.");
        }
    }
    
    
    // -- View requests ----------------------------------------------------------------------
    
    // -- Commands ---------------------------------------------------------------------------
    
    public abstract void createFxNode();
    
    public void saveAsOriginal() {
        this.originalFx = this.clone();
    }
    
    @Override
    public abstract FxContainer clone();
    
    /**
     * Calculate the coordinates of the FX node with middle point <tt>middlePoint</tt>. These
     * coordinates can differ per type of node. For example: rectangles have their coordinates
     * in their upper left corner, whereas circles have their coordinates in their center.
     * @param middlePoint The middle point of the FX node.
     * @return            The coordinates of the FX node.
     */
    //@ requires middlePoint != null;
    //@ ensures \result != null;
    protected abstract Point3D calculateCoordinates(Point3D middlePoint);
    //TODO: check if this is used at all.
    
    /**
     * Animate the JavaFX node to the point where its middle point is equal to 
     * <tt>middlePoint</tt>.
     * @param middlePoint The middle point of the FX node.
     * @param duration    The duration of the animation.
     * @return            The <tt>Transition</tt> that executes the movement.
     */
    //@ requires middlePoint != null && duration != null;
    //@ requires getFxNode() != null;
    //@ ensures \result != null;
    public abstract Transition animateToMiddlePoint(Point3D middlePoint, Duration duration);
    
    /**
     * Set the GreenMirror node to the point where its middle point is equal to 
     * <tt>middlePoint</tt>.
     * @param middlePoint The middle point of the FX node.
     */
    //@ requires middlePoint != null;
    public abstract void setToPositionWithMiddlePoint(Point3D middlePoint);
    
    /**
     * Set the JavaFX node to the point where its middle point is equal to <tt>middlePoint</tt>.
     * @param middlePoint The middle point of the FX node.
     */
    //@ requires middlePoint != null;
    //@ requires getFxNode() != null;
    public abstract void setFxToPositionWithMiddlePoint(Point3D middlePoint);
    
    /**
     * Create animations from a <tt>Map</tt> of values (from a JSON object, for example).
     * @param newMap      The <tt>Map</tt> with key-value pairs.
     * @param duration The duration for the animation of the changes.
     * @return         The <tt>Transition</tt> object that applies the changes.
     */
    //@ requires newMap != null && animationDuration != null;
    //@ ensures \result != null;
    public Transition animateFromMap(Map<String, Object> newMap, Duration duration) {
        ParallelTransition transitions = new ParallelTransition();
        String property = null;
        Object value = null;
        Object result = null;
        
        // Check per property if we received a change.
        // The newValues variable is used so the properties are already parsed.
        FxContainer newValues = this.clone();
        newValues.setFromMap(newMap);
        Map<String, Object> currentMap = this.toMap();
        
        try {
            // Loop through all entries in map.
            for (Map.Entry<String, Object> newEntry : newMap.entrySet()) {

                // Get property name and value.
                property = newEntry.getKey();
                value = newEntry.getValue();
                FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
                        getAnimatableProperties(), property);
                
                // Continue to the next if there is no FxPropertyWrapper or if the value is null.
                if (fxPropertyWrapper == null || value == null) {
                    continue;
                }
                // Also continue if the (map) value didn't change.
                //TODO: implement a more elegant solution for this comparison.
                /*TODO: fix the line below. This is not how it should work. Problem: newEntry.getValue() returns a (map) Object, so its 
                 * equals() method doens't work on other subclasses of Object.
                 * Possible solution: implement FxPropertyWrapper.equals(Object) and let its subclasses override.
                 */
                if (String.valueOf(value).equals(String.valueOf(currentMap.get(property)))) {
                    continue;
                }
                
                // Get animate method and execute with the cast value.
                result = fxPropertyWrapper.getAnimateMethod(this.getClass())
                                          .invoke(this, fxPropertyWrapper.cast(value), duration);
                
                // Notify the user if the animation method couldn't produce an animation.
                if (result == null) {
                    throw new IllegalStateException("The animate method was unable to produce "
                            + "an animation.");
                }
                
                // Add animation.
                transitions.getChildren().add((Transition) result);
            }
        } catch (IllegalAccessException | InvocationTargetException | IllegalStateException 
               | NoSuchMethodException e) {
            Log.add("Animating of JavaFX node property (" + property + ") failed: ", e);
        }
        
        return transitions;
    }
}
