package greenmirror;

import greenmirror.fxcontainers.RectangleFxContainer;
import greenmirror.fxpropertytypes.DoubleFxProperty;
import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.fxpropertytypes.StringFxProperty;
import greenmirror.server.DoublePropertyTransition;
import groovy.json.JsonOutput;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.ServiceLoader;
import java.util.Set;

import javafx.animation.FadeTransition;
import javafx.animation.ParallelTransition;
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
    
    /** All different prototypes. */
    private static Set<FxContainer> prototypes;

    // -- Instance variables -----------------------------------------------------------------
    
    private FxContainer originalFx;
    
    private javafx.scene.Node fxNode;
    
    private double rotate;
    private double opacity = 1.0;
    private String style;

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
 
    /**
     * @return The type of the <tt>FxContainer</tt>.
     */
    /*@ pure */ public String getType() {
        return getClass().getSimpleName().replace("FxContainer", "");
    }
 
    /**
     * Get the previously saved, original <tt>FxContainer</tt>.
     * @return The original saved <tt>FxContainer</tt>; <tt>null</tt> if none was saved.
     */
    /*@ pure */ public FxContainer getOriginalFx() {
        return this.originalFx;
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
        Map<String, Object> map = new LinkedHashMap<>();
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
    
    /**
     * Returns the result of {@link #toMap()} without any positioning data. It removes x, y, z, 
     * centerX, centerY and centerZ. If an extending class has other positioning data, it should 
     * override this method.
     * @return The property map of this <tt>FxContainer</tt> without positioning data.
     */
    //@ ensures \result != null;
    /*@ pure */ public Map<String, Object> toMapWithoutPositionData() {
        Map<String, Object> map = toMap();
        map.remove("x");
        map.remove("y");
        map.remove("z");
        map.remove("centerX");
        map.remove("centerY");
        map.remove("centerZ");
        return map;
    }
    
    // test DoubleFxProperty
    public static void main1(String[] args) {
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
     * Calculate the adjustment for a point relative to the middle point of the current node.
     * @param obj The point relative to the middle point of the current node. Only the x and y
     *            coordinates are taken into account.
     * @return    The new point.
     */
    //@ requires obj != null;
    //@ ensures \result != null;
    /*@ pure */ public Point3D getPointAdjustedForRotation(Point3D obj) {
        final double angle = Math.toRadians(getRotate());
        final Point3D pivotPoint = calculatePoint(Placement.MIDDLE);
        final Point3D relativePoint = obj.subtract(pivotPoint);
        
        final double cos = Math.cos(angle);
        final double sin = Math.sin(angle);
        
        return pivotPoint.add(cos * relativePoint.getX() - sin * relativePoint.getY(),
                              sin * relativePoint.getX() + cos * relativePoint.getY(), 0);
    }
    
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
    
    public FxContainer setRotateBy(double value) {
        this.rotate += value;
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
    
    public RotateTransition animateRotate(double value, Duration duration) {
        return new RotateTransition(duration, getFxNode(), value);
    }
    
    public FadeTransition animateOpacity(double value, Duration duration) {
        FadeTransition transition = new FadeTransition(duration, getFxNode());
        transition.setToValue(value);
        return transition;
    }
    
    public FadeTransition animateOpacity(double from, double to, Duration duration) {
        FadeTransition transition = new FadeTransition(duration, getFxNode());
        transition.setFromValue(from);
        transition.setToValue(to);
        return transition;
    }
    
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    private static Set<FxContainer> getPrototypes() {
        return prototypes;
    }
    
    /**
     * Instantiate a new <tt>FxContainer</tt>. It does this by using <tt>ServiceLoader</tt>
     * (lazily).
     * @param type The type, which should be the same as the class name in the 
     *             <tt>greenmirror.fxcontainers</tt> package, appended with <tt>FxContainer</tt>.
     *             The first letter will be capitalized.
     * @return     The new instance.
     * @throws IllegalArgumentException If the passed type is invalid.
     */
    //@ requires type != null;
    public static FxContainer getNewInstance(String type) {
        
        if (getPrototypes() == null) {
            prototypes = new HashSet<FxContainer>();
            for (FxContainer fxContainer : ServiceLoader.load(FxContainer.class)) {
                getPrototypes().add(fxContainer);
            }
        }
        
        String simpleClassName = Character.toUpperCase(type.charAt(0)) + type.substring(1)
                + "FxContainer";
        
        for (FxContainer fxContainerPrototype : getPrototypes()) {
            if (simpleClassName.equals(fxContainerPrototype.getClass().getSimpleName())) {
                return fxContainerPrototype.clone();
            }
        }

        throw new IllegalArgumentException("The passed FX type (" + type + ") is invalid.");
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
    

    
    /**
     * A <tt>Transition</tt> class that animates the change of the rotation. The default 
     * <tt>RotateTransition</tt> class isn't used because it's buggy when playing back 
     * transitions.
     * 
     * @author Karim El Assal
     */
    public static class RotateTransition extends DoublePropertyTransition<javafx.scene.Node> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected RotateTransition(Duration duration, javafx.scene.Node node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getRotate();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setRotate(value);
        }
    }
}
