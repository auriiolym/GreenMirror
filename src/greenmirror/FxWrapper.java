package greenmirror;

import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.fxpropertywrappers.StringFxProperty;
import greenmirror.placements.EdgePlacement;
import greenmirror.server.DoublePropertyTransition;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Random;
import java.util.ServiceLoader;
import java.util.Set;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.util.Duration;

/**
 * A wrapper class for handling JavaFX nodes.
 * 
 * It registers virtual values of the properties of the FX node it holds. This is done so
 * animations can be created (server side) without directly reading from or writing to the
 * relevant FX node.
 * Furthermore, it contains auxiliary methods for usage by its subclasses.
 * <p>
 * <b>Adding a new <code>FxWrapper</code></b>
 * <ol>
 *  <li>Create a new subclass of <code>FxWrapper</code> or {@link greenmirror.FxShapeWrapper}.</li>
 *  <li>Implement and override all relevant methods.</li>
 *  <li>Add the properties you want (see below).</li>
 *  <li>Add the new binary class name on a new line to 
 *      <code>META-INF/services/greenmirror.FxWrapper</code>.</li>
 *  <li>Recompile.</li>
 * </ol>
 * <p>
 * <b>Adding properties to an <code>FxWrapper</code></b>
 * <ol>
 *  <li>Create a new {@link greenmirror.FxPropertyWrapper} if it doesn't exist yet.</li>
 *  <li>Add the property to {@link #getAnimatableProperties()} or 
 *      {@link #getChangableProperties()}.</li>
 *  <li>Add getter(s).</li>
 *  <li>Add setter(s).</li>
 *  <li>If your property can be animated (and thus you added it to 
 *      {@link #getAnimatableProperties()}) and it hasn't got an <code>Animation</code>
 *      for it yet, create it. For examples, see {@link RotateTransition} and
 *      {@link greenmirror.fxwrappers.ImageFxWrapper.ImageTransition}.</li>
 *  <li>If your property can be animated, add animate method(s) (like 
 *      <code>animatePROPERTY(double, Duration)</code>) that create the animations that
 *      change the property value on the FX node.</li>
 *  <li>If the user needs to create instances of new types in his Groovy script to make use
 *      of the property, add an import to
 *      {@link greenmirror.client.GroovyScriptModelInitializer#IMPORTS}.</li>
 *  <li>Recompile.</li>
 * </ol>
 * A property can thus be one of two types:
 * <ul>
 *  <li>a property that can be set only once (e.g.: the style property of any JavaFX node). This
 *      is because the property then can not be animated. Follow steps 1-4 and 7 and 8 of the
 *      above list. In a Groovy script it can only be set by first creating the node and its
 *      FX appearance and then adding it to GreenMirror (by using <code>addNode(Node)</code>
 *      or <code>addNodes(Node...)</code>).</li>
 *  <li>a property that can be set and changed (e.g.: the rotate property of any JavaFX node).
 *      This means the property can be animated. Follow all steps of the above list.</li>
 * </ul>
 * 
 * @author Karim El Assal
 */
public abstract class FxWrapper extends Observable implements Cloneable {
    
    // -- Class variables --------------------------------------------------------------------
    
    /** The different prototypes. */
    private static Set<FxWrapper> prototypes;
    

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The original FxWrapper, set when this FxWrapper will change due to a relation with a 
     * temporary FX.
     */
    private FxWrapper originalFxWrapper;
    
    /** The JavaFX node this FxWrapper created for. */
    private javafx.scene.Node fxNode;
    
    /** The virtual rotation of the FX node. */
    private double rotate;
    
    /** The virtual opacity of the FX node. */
    //@ private invariant opacity >= 0.0 && opacity <= 1.0;
    private double opacity = 1.0;
    
    /** The virtual CSS style of the FX node. */
    private String style;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
 
    /**
     * Returns the type of this <code>FxWrapper</code>. It defaults to the class name with the
     * "FxWrapper" part removed.
     * 
     * @return the type of this <code>FxWrapper</code>
     */
    /*@ pure non_null */ public String getType() {
        return getClass().getSimpleName().replace("FxWrapper", "");
    }
 
    /**
     * @return the previously saved, original <code>FxWrapper</code>;
     *         <code>null</code> if none was saved
     */
    /*@ pure */ public FxWrapper getOriginalFxWrapper() {
        return this.originalFxWrapper;
    }
    
    /** @return the JavaFX node that this <code>FxWrapper</code> was created for */
    /*@ pure */ public javafx.scene.Node getFxNode() {
        return this.fxNode;
    }
    
    /** @return the virtual rotation property value of the FX node */
    /*@ pure */ public double getRotate() {
        return this.rotate;
    }
    
    /** @return the virtual opacity property value of the FX node */
    //@ ensures \result >= 0.0 && \result <= 1.0;
    /*@ pure */ public double getOpacity() {
        return this.opacity;
    }
    
    /** @return the virtual CSS style property value of the FX node */
    /*@ pure */ public String getStyle() {
        return this.style;
    }

    /**
     * Returns a mapping of the properties of this <code>FxWrapper</code> that are defined
     * in {@link #getChangableProperties()}. This should contain all relevant information to 
     * construct the FX node.
     * 
     * Every property's <code>FxPropertyWrapper</code> determines how the values will be mapped.
     * 
     * @return a map of this <code>FxWrapper</code>'s properties
     */
    //@ ensures \result.containsKey("type") && \result.containsKey("opacity");
    //@ ensures \result.containsKey("rotate") && \result.containsKey("style");
    /*@ pure non_null */ public Map<String, Object>  toMap() {
        final Map<String, Object> map = new LinkedHashMap<String, Object>();
        map.put("type", getType());
        
        // Loop through relevant properties.
        for (FxPropertyWrapper fxProperty : getChangableProperties()) {
            final String var = fxProperty.getPropertyName();
            
            try {
                // Execute getter.
                final Object result = fxProperty.getGetMethod(this.getClass()).invoke(this);
                
                // Put result into map.
                map.put(var, fxProperty.castToMapValue(result));
                
            } catch (NoSuchMethodException | InvocationTargetException | IllegalAccessException e) {
                throw new RuntimeException("Something went horribly wrong while creating the map "
                        + "of " + getType() + "FxWrapper. It's about the " + var + " property. "
                        + "You should check if the get method exists.", e);
            }
        }
        return map;
    }
    
    /**
     * Returns the result of {@link #toMap()} without any positioning data. It removes x, y, z, 
     * centerX, centerY and centerZ. If a subclass has other positioning data, it should 
     * override this method and remove the relevant data.
     * 
     * @return the property map of this <code>FxWrapper</code> without positioning data
     * @see    #toMap()
     */
    //@ ensures !\result.containsKey("x") && !\result.containsKey("y") && !\result.containsKey("z");
    //@ ensures !\result.containsKey("centerX") && !\result.containsKey("centerY");
    //@ ensures !\result.containsKey("centerZ");
    /*@ pure non_null */ public Map<String, Object> toMapWithoutPositionData() {
        final Map<String, Object> map = toMap();
        map.remove("x");
        map.remove("y");
        map.remove("z");
        map.remove("centerX");
        map.remove("centerY");
        map.remove("centerZ");
        return map;
    }
    
    /**
     * Returns the JavaFX node's properties that can be animated (and thus: can be changed
     * during a transition). All animatable properties also are changable properties. These
     * differ per subclass, but always contain the ones defined by <code>FxWrapper</code>.
     * Overriding subclasses should also execute this method.
     * 
     * @return the properties that can be animated
     * @see    #getChangableProperties()
     * @see    FxPropertyWrapper
     */
    //@ ensures \result.size() >= 2;
    /*@ pure non_null */ protected List<FxPropertyWrapper> getAnimatableProperties() {
        return new ArrayList<FxPropertyWrapper>() {
            {
                add(new DoubleFxProperty("rotate"));
                add(new DoubleFxProperty("opacity"));
            }
        };
    }
    
    /**
     * Returns the properties of the JavaFX node that can be changed using this
     * <code>FxWrapper</code>. That they can be changed does <b>not</b> mean they
     * can be animated. If a property is only changable, but not animatable, it can
     * only be set once.
     * 
     * @return the properties that can be changed by using this <code>FxWrapper</code>
     */
    /*@ ensures \result.size() >= 3;
      @ ensures (\forall int i; i >= 0 && i < \result.size(); 
      @         getAnimatableProperties().contains(\result.get(i))); */
    /*@ pure non_null */ protected List<FxPropertyWrapper> getChangableProperties() {
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(getAnimatableProperties());
                add(new StringFxProperty("style"));
            }
        };
    }
    
    /**
     * Returns a string description of this <code>FxWrapper</code>. It retrieves the map
     * of all properties, removes any image values (because that would mean a long base64
     * encoded string) and returns a string representation.
     * 
     * @return a string representation of this <code>FxWrapper</code>
     */
    @Override
    /*@ pure non_null */ public String toString() {
        final Map<String, Object> map = toMap();
        if (map.containsKey("image") && map.get("image") != null 
                && ((String) map.get("image")).length() > 40) {
            map.put("image", "--removed for convenience (because it was set)--");
        }
        return getType() + map.toString();
    }
    
    /**
     * Checks if the position of the FX node was set. Usually it checks if the x and y values 
     * are set. This method is abstract because not all JavaFX nodes work with the
     * <code>getX</code> and <code>getY</code> methods.
     * 
     * @return <code>true</code> if the position was set
     */
    /*@ pure */ public abstract boolean isPositionSet();
    
    /**
     * Calculate the adjustment for a point relative to the middle point of the current node.
     * 
     * @param obj the point relative to the middle point of the current node. Only the x and y
     *            coordinates are taken into account.
     * @return    the new point
     * @throws    NullPointerException if <code>obj</code> is <code>null</code>
     */
    /*@ pure non_null */ public Point3D getPointAdjustedForRotation(/*@ non_null */ Point3D obj) {
        if (obj == null) {
            throw new NullPointerException("relative point" 
                    + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        final Point3D pivotPoint = calculatePoint(Placement.MIDDLE);
        final double angle = Math.toRadians(getRotate());
        final Point3D relativePoint = obj.subtract(pivotPoint);
  
        final double cos = Math.cos(angle);
        final double sin = Math.sin(angle);
        
        return pivotPoint.add(
                new Point3D(cos * relativePoint.getX() - sin * relativePoint.getY(),
                            sin * relativePoint.getX() + cos * relativePoint.getY(), 0));
    }
    
    /**
     * Calculates the absolute point with of a specified <code>Placement</code> on the 
     * JavaFX node. E.g.: if <code>this</code> is a <code>RectangleFxWrapper</code> 
     * representing a 100x100 rectangle at position (10,10) of the canvas,
     * <code>calculatePoint(Placement.MIDDLE)</code> would result in point (60,60). 
     * 
     * @param placement the position of placement which should be calculated.
     * @return          the absolute point
     */
    /*@ pure non_null */ public abstract Point3D calculatePoint(/*@ non_null */Placement placement);
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * Sets the JavaFX node. This should only be done once: when the JavaFX node is created
     * and added to the visualizer.
     *  
     * @param node
     */
    //@ ensures getFxNode() == node;
    protected void setFxNode(/*@ non_null */ javafx.scene.Node node) {
        this.fxNode = node;
    }
    
    /**
     * Sets the virtual rotation of the JavaFX node and notifies the observer (the 
     * GreenMirror node, if this <code>FxWrapper</code> is part of a GreenMirror node). 
     * 
     * @param value the new rotation in degrees
     * @return      <code>this</code>
     * @see         javafx.scene.Node#setRotate(double)
     */
    //@ ensures getRotate() == value;
    //@ ensures \result == this;
    public FxWrapper setRotate(double value) {
        this.rotate = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Adds <code>value</code> to the virtual rotation of the JavaFX node and notifies the 
     * observer (the GreenMirror node, if this <code>FxWrapper</code> is part of a GreenMirror 
     * node) about it. 
     * 
     * @param value the rotation to add to the current rotation (in degrees)
     * @return      <code>this</code>
     * @see         #setRotate(double)
     * @see         javafx.scene.Node#setRotate(double)
     */
    //@ ensures getRotate() == \old(getRotate()) + value;
    //@ ensures \result == this;
    public FxWrapper setRotateBy(double value) {
        return setRotate(getRotate() + value);
    }
    
    /**
     * Sets the virtual opacity of the JavaFX node and notifies the observer (the 
     * GreenMirror node, if this <code>FxWrapper</code> is part of a GreenMirror node).
     * The opacity should be a value between (and including) 0 and 1.0. 
     * 
     * @param value the new opacity
     * @return      <code>this</code>
     * @see         javafx.scene.Node#setOpacity(double)
     * @throws IllegalArgumentException if the received value was invalid.
     */
    //@ requires value >= 0.0 && value <= 1.0;
    //@ ensures getOpacity() == value;
    //@ ensures \result == this;
    public FxWrapper setOpacity(double value) {
        if (value < 0 || value > 1.0) {
            throw new IllegalArgumentException("invalid value for the opacity: " + value);
        }
        this.opacity = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual CSS style of the JavaFX node and notifies the observer (the 
     * GreenMirror node, if this <code>FxWrapper</code> is part of a GreenMirror node).
     * 
     * @param value the new css style
     * @return      <code>this</code>
     * @throws NullPointerException if <code>value</code> is <code>null</code>
     */
    //@ ensures getStyle() == value;
    //@ ensures \result == this;
    public FxWrapper setStyle(/*@ non_null */ String value) {
        if (value == null) {
            throw new NullPointerException("style value" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        this.style = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the virtual JavaFX node properties in this <code>FxWrapper</code> from a map.
     * 
     * @param newValues a property-value map with the new values
     * @throws NullPointerException if <code>newValues</code> is <code>null</code>
     */
    //@ ensures newValues.equals(toMap());
    public void setFromMap(/*@ non_null */ Map<String, Object> newValues) {
        if (newValues == null) {
            throw new NullPointerException("new value map" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        
        String property = null;
        try {
            // Loop through all to-be-set entries in newValues.
            for (Map.Entry<String, Object> entry : newValues.entrySet()) {
                
                // Get property name and value.
                property = entry.getKey();
                final Object value = entry.getValue();
                final FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
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
            Log.add("Automatic setting of FX wrapper property (" + property + ") failed: ", e);
        }
    }
    
    /**
     * Sets the properties of the JavaFX node from a map.
     * 
     * @param newValues a property-value map with the new values
     * @throws IllegalStateException if this wrapper does not have a JavaFX node
     * @throws NullPointerException  if <code>newValues</code> is <code>null</code>
     */
    //@ requires getFxNode() != null;
    public void setFxNodeValuesFromMap(/*@ non_null */ Map<String, Object> newValues) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (newValues == null) {
            throw new NullPointerException("new value map" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        
        String property = null;
        Object value = null;
        try {
            // Loop through all to-be-set entries in newValues.
            for (Map.Entry<String, Object> entry : newValues.entrySet()) {
                

                // Get property name and value.
                property = entry.getKey();
                value = entry.getValue();
                final FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
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
    
    /**
     * Creates the animation that changes the rotate property of the JavaFX node to 
     * <code>value</code>.
     * 
     * @param value    the angle (in degrees) to rotate to
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @throws         NullPointerException  if <code>duration</code> is <code>null</code>
     * @see            RotateTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure non_null*/ public RotateTransition animateRotate(double value, 
            /*@ non_null */ Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (duration == null) {
            throw new NullPointerException("duration" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        return new RotateTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the opacity property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the opacity to change to. This has to be a value between (and including)
     *                 0 and 1.0.
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if <code>value</code> is invalid
     * @throws         NullPointerException     if <code>duration</code> is <code>null</code>
     * @see            FadeTransition
     */
    //@ requires getFxNode() != null && value >= 0 && value <= 1.0;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure non_null*/ public FadeTransition animateOpacity(double value, 
            /*@ non_null */ Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (value < 0 || value > 1.0) {
            throw new IllegalArgumentException("invalid opacity value: " + value);
        }
        if (duration == null) {
            throw new NullPointerException("duration" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        return new FadeTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the opacity property of the JavaFX node from 
     * <code>fromValue</code> to <code>toValue</code>.
     * 
     * @param fromValue the opacity to change to. This has to be a value between (and including)
     *                  0 and 1.0.
     * @param toValue   the opacity to change to. This has to be a value between (and including)
     *                  0 and 1.0.
     * @param duration  the duration of the animation
     * @return          the JavaFX <code>Animation</code> that animates the change
     * @throws          IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws          IllegalArgumentException if <code>fromValue</code> or <code>toValue</code>
     *                                           is invalid
     * @throws          NullPointerException     if <code>duration</code> is <code>null</code>
     * @see             #animateOpacity(double, Duration)
     * @see             FadeTransition
     */
    //@ requires getFxNode() != null && fromValue >= 0 && fromValue <= 1.0;
    //@ requires toValue >= 0 && toValue <= 1.0;
    //@ ensures \result.getToValue() == toValue && \result.getFromValue() == fromValue;
    //@ ensures \result.getDuration() == duration && \result.getNode() == getFxNode();
    /*@ pure non_null*/ public FadeTransition animateOpacity(double fromValue, double toValue, 
            /*@ non_null */Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (fromValue < 0 || fromValue > 1.0) {
            throw new IllegalArgumentException("invalid opacity fromValue: " + fromValue);
        }
        if (toValue < 0 || toValue > 1.0) {
            throw new IllegalArgumentException("invalid opacity toValue: " + toValue);
        }
        if (duration == null) {
            throw new NullPointerException("duration" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        final FadeTransition transition = new FadeTransition(duration, getFxNode(), toValue);
        transition.setFromValue(fromValue);
        return transition;
    }
    
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Calculates the coordinates of a placement on a rectangle given the width and height of the
     * rectangle. The origin of the coordinate system of the returned point lies in the upper left
     * corner of the rectangle.
     * 
     * @param width     the width of the rectangle
     * @param height    the height of the rectangle
     * @param placement the placement on the rectangle
     * @return          the coordinates of the placement relative to the origin of the rectangle
     * @throws IllegalArgumentException if the width or height is negative
     * @see             greenmirror.Placement
     */
    //@ requires width >= 0 && height >= 0;
    /*@ pure non_null */ public static Point3D calculatePointOnRectangle(double width, 
            double height, /*@ non_null */ Placement placement) {
        if (width < 0 || height < 0) {
            throw new IllegalArgumentException("width and height can't be negative.");
        }
        
        // Default vaules.
        double calcX = 0;
        double calcY = 0;
        
        switch (placement.toString()) {
        case "None": default:
            return Point3D.ZERO;
        case "Random":
            calcX = GreenMirrorUtils.getRandomBetween(0, width);
            calcY = GreenMirrorUtils.getRandomBetween(0, height);
            break;
        case "Custom": case "Middle":
            calcX = width / 2;
            calcY = height / 2;
            break;
        case "Edge":
            /**
             * Source of the equations:
             * http://
             * stackoverflow.com/questions/4061576/finding-points-on-a-rectangle-at-a-given-angle
             */
            // Avert division by zero errors.
            if (height == 0) {
                height = 0.0000001; 
            }
            final double degrees = ((EdgePlacement) placement).getAngle();
            // Boundary angles, starting from the top right corner, going clockwise.
            final double b1 = Math.toDegrees(Math.atan(width / height));
            final double b2 = 180 - b1;
            final double b3  = b1 + 180;
            final double b4  = b2 + 180;
            boolean verticalQuadrant = true;
            boolean primaryQuadrant = true; // Top and right quadrants are primary.
            // First quadrant: right
            if (degrees > b1 && degrees <= b2) {
                verticalQuadrant = false;
            } else
            // Second quadrant: bottom
            if (degrees > b2 && degrees < b3) {
                primaryQuadrant = false;
            } else
            // Third quadrant: left
            if (degrees >= b3 && degrees <= b4) {
                verticalQuadrant = false;
                primaryQuadrant = false;
            }
            // Fourth quadrant: top
            //  degrees > b4 || degrees < b1
            
            // Get the angle in radians, shift the origin and normalize it.
            // TODO: check if normalization is necessary.
            final double radians = Math.toRadians(
                    new EdgePlacement(360 + 90 - degrees).getAngle());
            if (verticalQuadrant) {
                calcY = primaryQuadrant ? 0 : height;
                calcX = width / 2 + width / (2 * Math.tan(radians)); 
            } else {
                calcX = primaryQuadrant ? width : 0;
                calcY = height / 2 + height / 2 * Math.tan(radians);
            }
            break;
        case "EdgeTop":
            calcX = width / 2;
            break;
        case "EdgeRight":
            calcX = width;
            calcY = height / 2;
            break;
        case "EdgeBottom":
            calcX = width / 2;
            calcY = height;
            break;
        case "EdgeLeft":
            calcY = height / 2;
            break;
        case "CornerTopLeft":
            break;
        case "CornerTopRight":
            calcX = width;
            break;
        case "CornerBottomRight":
            calcX = width;
            calcY = height;
            break;
        case "CornerBottomLeft":
            calcY = height;
            break;
        }
        return new Point3D(calcX, calcY, 0).add(placement.getRelativePosition());
    }
    
    /**
     * @return the prototype <code>FxWrapper</code> subclasses
     */
    /*@ pure */ private static Set<FxWrapper> getPrototypes() {
        return prototypes;
    }
    
    /**
     * Returns a new <code>FxWrapper</code> instance. On the first call, a set of prototypes of
     * all available <code>FxWrapper</code>s is created by using 
     * {@link java.util.ServiceLoader ServiceLoader}. This method returns a clone of the
     * prototype of the type passed via <code>type</code>.
     * 
     * @param type the type, which should be the same as the class name in the 
     *             <code>greenmirror.fxwrappers</code> package, appended with 
     *             <code>FxWrapper</code>. The first letter will be capitalized.
     * @return     he new instance
     * @throws IllegalArgumentException if the passed type is invalid
     * @throws NullPointerException     if <code>type</code> is <code>null</code>
     * @see        FxWrapper
     * @see        java.util.ServiceLoader
     */
    /*@ non_null */ public static FxWrapper getNewInstance(/*@ non_null */ String type) {
        if (type == null) {
            throw new NullPointerException("FxWrapper type" 
                    + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        
        // Get prototypes if we haven't yet.
        if (getPrototypes() == null) {
            prototypes = new HashSet<FxWrapper>();
            for (FxWrapper fxWrapper : ServiceLoader.load(FxWrapper.class)) {
                getPrototypes().add(fxWrapper);
            }
        }
        
        final String simpleClassName = GreenMirrorUtils.capitalizeFirstChar(type) + "FxWrapper";
        
        for (FxWrapper fxWrapperPrototype : getPrototypes()) {
            if (simpleClassName.equals(fxWrapperPrototype.getClass().getSimpleName())) {
                return fxWrapperPrototype.clone();
            }
        }

        throw new IllegalArgumentException("the passed FX type (" + type + ") is invalid.");
    }
    
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Creates the JavaFX node and makes it available via {@link #getFxNode()}.
     */
    //@ ensures getFxNode() != null;
    public abstract void createFxNode();
    
    /**
     * Saves a (shallow) copy of this <code>FxWrapper</code> as the original and makes it
     * available via {@link #getOriginalFxWrapper()}.
     */
    //@ ensures getOriginalFxWrapper() != null && getOriginalFxWrapper().toMap().equals(toMap());
    public void saveAsOriginal() {
        this.originalFxWrapper = this.clone();
    }
    
    /**
     * Creates a shallow copy of this <code>FxWrapper</code>: only the property values are copied.
     */
    //@ ensures \result.toMap().equals(toMap());
    /*@ pure non_null */ @Override public abstract FxWrapper clone();
    
    /**
     * Calculates the coordinates of the FX node's origin when its middle point is equal to
     * <code>nodeMiddlePoint</code>. These coordinates can differ per type of node. 
     * <p>
     * For example: rectangles have their origin coordinates in their upper left corner. 
     * This method would use the following calculation to calculate the x coordinate:
     * <code>double coordinateX = nodeMiddlePoint.getX() - getWidth() / 2;</code>
     * Similarly, an <code>FxWrapper</code> wrapping a circle node would return the same
     * values as <code>nodeMiddlePoint</code>.
     * 
     * @param nodeMiddlePoint the middle point of the FX node
     * @return                the origin coordinates of the FX node
     */
    /*@ pure non_null */ protected abstract Point3D calculateOriginCoordinates(
            /*@ non_null */ Point3D nodeMiddlePoint);
    
    /**
     * Creates the animation that changes the position of the JavaFX node to the point where its
     * middle point is equal to <code>middlePoint</code>.
     * 
     * @param middlePoint the middle point of the FX node
     * @param duration    the duration of the animation
     * @return            the JavaFX <code>Animation</code> that animates the change
     */
    //@ requires middlePoint != null && duration != null;
    //@ requires getFxNode() != null;
    //@ ensures \result != null;
    /*@ pure non_null */ public abstract Transition animateToMiddlePoint(
            /*@ non_null */ Point3D middlePoint, /*@ non_null */ Duration duration);
    
    /**
     * Sets the virtual positioning property values to the point where its middle point is equal 
     * to <code>nodesNewMiddlePoint</code>.
     * 
     * @param nodesNewMiddlePoint the new middle point indicating the positioning values of 
     *                            this wrapper
     */
    //@ ensures nodesNewMiddlePoint.equals(calculatePoint(Placement.MIDDLE));
    public abstract void setToPositionWithMiddlePoint(
            /*@ non_null */ Point3D nodesNewMiddlePoint);
    
    /**
     * Sets the JavaFX node positioning property values to the point where its middle point is
     * equal to <code>nodesNewMiddlePoint</code>.
     * 
     * @param nodesNewMiddlePoint the new middle point of the FX node
     */
    //@ requires getFxNode() != null;
    public abstract void setFxToPositionWithMiddlePoint(
            /*@ non_null */ Point3D nodesNewMiddlePoint);
    
    /**
     * Creates animations from a property-value map (from a JSON object, for example). The 
     * animations are stored in a <code>ParallelTransition</code>, so they're all applied
     * concurrently.
     * <p>
     * Only properties from {@link #getAnimatableProperties()} can be animated. If others
     * are present in <code>newValuesMap</code> they're ignored.
     * 
     * @param newValuesMap   the map with property-value pairs
     * @param duration the total duration for the animations
     * @return         the JavaFX <code>Animation</code> that animates the changes
     * @throws IllegalStateException if <code>getFxNode()</code> returns <code>null</code>
     * @throws NullPointerException  if <code>newValuesMap</code> or <code>duration</code>
     *                               is <code>null</code>
     */
    /*@ pure non_null */ public ParallelTransition animateFromMap(
            /*@ non_null */ Map<String, Object> newValuesMap, /*@ non_null */ Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (newValuesMap == null || duration == null) {
            throw new NullPointerException("duration and new values map" 
                    + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        
        final ParallelTransition transitions = new ParallelTransition();
        String property = null;
        Object value = null;
        
        // Check per property if we received a change.
        // The newValues variable is used so the properties are already parsed.
        final FxWrapper newValues = this.clone();
        newValues.setFromMap(newValuesMap);
        final Map<String, Object> currentValuesMap = this.toMap();
        
        try {
            // Loop through all entries in newValuesMap.
            for (Map.Entry<String, Object> newEntry : newValuesMap.entrySet()) {

                // Get property name and value.
                property = newEntry.getKey();
                value = newEntry.getValue();
                final FxPropertyWrapper fxPropertyWrapper = FxPropertyWrapper.getFromList(
                        getAnimatableProperties(), property);
                
                // Continue to the next if there is no FxPropertyWrapper or if the value is null.
                if (fxPropertyWrapper == null || value == null) {
                    continue;
                }
                // Also continue if the (map) value didn't change.
                if (String.valueOf(value).equals(String.valueOf(currentValuesMap.get(property)))) {
                    continue;
                }
                
                // Get animate method and execute with the cast value.
                final Object result = fxPropertyWrapper.getAnimateMethod(this.getClass())
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
            Log.add("Animating of JavaFX node property (" + property + " with value:" 
                    + String.valueOf(value) + ") failed: ", e);
        }
        
        return transitions;
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the rotation. The default 
     * <code>RotateTransition</code> class isn't used because it's buggy when playing back 
     * transitions.
     * 
     * @author Karim El Assal
     */
    public static class RotateTransition extends DoublePropertyTransition<javafx.scene.Node> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)
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

    
    /**
     * A <code>Transition</code> class that animates the change in opacity. The default 
     * <code>FadeTransition</code> class isn't used because it's buggy when playing back 
     * transitions.
     * 
     * @author Karim El Assal
     */
    public static class FadeTransition extends DoublePropertyTransition<javafx.scene.Node> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)
         */
        protected FadeTransition(Duration duration, javafx.scene.Node node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getOpacity();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setOpacity(value);
        }
    }
}
