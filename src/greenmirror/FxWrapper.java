package greenmirror;

import greenmirror.fxwrappers.RectangleFxWrapper;
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
import java.util.Random;
import java.util.ServiceLoader;
import java.util.Set;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.paint.Color;
import javafx.util.Duration;

/**
 * 
 * 
 * @author Karim El Assal
 */
public abstract class FxWrapper extends Observable implements Cloneable {
    
    // -- Enumerations -----------------------------------------------------------------------

    // -- Exceptions -------------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------
    
    /** All different prototypes. */
    private static Set<FxWrapper> prototypes;

    // -- Instance variables -----------------------------------------------------------------
    
    private FxWrapper originalFx;
    
    private javafx.scene.Node fxNode;
    
    private double rotate;
    private double opacity = 1.0;
    private String style;

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
 
    /**
     * @return The type of the <tt>FxWrapper</tt>.
     */
    /*@ pure */ public String getType() {
        return getClass().getSimpleName().replace("FxWrapper", "");
    }
 
    /**
     * Get the previously saved, original <tt>FxWrapper</tt>.
     * @return The original saved <tt>FxWrapper</tt>; <tt>null</tt> if none was saved.
     */
    /*@ pure */ public FxWrapper getOriginalFx() {
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
     * @return The property map of this <tt>FxWrapper</tt> without positioning data.
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
        RectangleFxWrapper rect = new RectangleFxWrapper();
        rect.setX(4);
        rect.setY(1);
        rect.setWidth(2);
        rect.setHeight(3);
        rect.setFill(Color.RED);
        Map<String, Object> map = rect.toMap();
        System.out.println(JsonOutput.prettyPrint(JsonOutput.toJson(map)));
        
        RectangleFxWrapper rect2 = new RectangleFxWrapper();
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
     * @return A String representation of this FxWrapper.
     */
    @Override
    /*@ pure */ public String toString() {
        Map<String, Object> map = toMap();
        if (map.containsKey("image") && map.get("image") != null 
                && ((String) map.get("image")).length() > 40) {
            map.put("image", "--removed for convenience (it was set)--");
        }
        String str = getClass().getSimpleName() + map.toString();
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
        final Point3D pivotPoint = calculatePoint(new Placement.Middle());
        final double angle = Math.toRadians(getRotate());
        final Point3D relativePoint = obj.subtract(pivotPoint);
  
        final double cos = Math.cos(angle);
        final double sin = Math.sin(angle);
        
        return pivotPoint.add(
                new Point3D(cos * relativePoint.getX() - sin * relativePoint.getY(),
                            sin * relativePoint.getX() + cos * relativePoint.getY(), 0));
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
    
    public FxWrapper setRotate(double value) {
        this.rotate = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxWrapper setRotateBy(double value) {
        this.rotate += value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxWrapper setOpacity(double value) {
        this.opacity = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxWrapper setStyle(String value) {
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
            Log.add("Automatic setting of FX wrapper property (" + property + ") failed: ", e);
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
        return new FadeTransition(duration, getFxNode(), value);
    }
    
    public FadeTransition animateOpacity(double from, double to, Duration duration) {
        FadeTransition transition = new FadeTransition(duration, getFxNode(), to);
        transition.setFromValue(from);
        return transition;
    }
    
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * http://stackoverflow.com/questions/4061576/finding-points-on-a-rectangle-at-a-given-angle
     * @param width
     * @param height
     * @param placement
     * @return
     */
    public static Point3D calculatePointOnRectangle(double width, double height, 
            Placement placement) {
        
        double calcX = 0;
        double calcY = 0;
        
        switch (placement.toString()) {
        case "None": default:
            return Point3D.ZERO;
        case "Random":
            Random random = new Random();
            double minX = 0;
            double maxX = width;
            double minY = 0;
            double maxY = height;

            calcX = minX + random.nextDouble() * (maxX - minX);
            calcY = minY + random.nextDouble() * (maxY - minY);
            break;
        case "Custom": case "Middle":
            calcX = width / 2;
            calcY = height / 2;
            break;
        case "Edge":
            if (height == 0) {
                height = 0.0000001; // Avert division by zero errors.
            }
            final double degrees = ((Placement.Edge) placement).getAngle();
            // Boundary angles, starting from the top right corner, going clockwise.
            final double b1 = Math.toDegrees(Math.atan(width / height));
            final double b2 = 180 - b1;
            final double b3  = b1 + 180;
            final double b4  = b2 + 180;
            boolean verticalQuadrant = true;
            boolean primaryQuadrant = true;
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
                    new Placement.Edge(360 + 90 - degrees).getAngle());
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
    
    public static void main3(String[] args) {
        double[] tests = {0, 45, 90, 180, 270, 359};
        int[][] results = {{50,0},{100,0},{100,50},{50,100},{0,50},{49,0}};
        for (int i = 0; i < tests.length; i++) {
            Point3D p = calculatePointOnRectangle(100, 100, new Placement.Edge(tests[i]));
            if (Math.round(p.getX()) == results[i][0] 
                    && Math.round(p.getY()) == results[i][1]) {
                System.out.println("success (" + tests[i] + ")");
            } else {
                System.out.println("fail (" + tests[i] + "): " + p.toString());
                System.out.println("needed: [x = " + results[i][0] + ", y = " + results[i][1] + "]");
            }
            System.out.println();
            System.out.println();
        }
        
        for (int i = 0; i < tests.length; i++) {
            double result = 360 - tests[i] + 90;
            System.out.println(tests[i] + " becomes " + new Placement.Edge(result).getAngle());
        }
        
    }
    
    public static double getRandomBetween(double min, double max) {
        return min + new Random().nextDouble() * (max - min);
    }
    
    private static Set<FxWrapper> getPrototypes() {
        return prototypes;
    }
    
    /**
     * Instantiate a new <tt>FxWrapper</tt>. It does this by using <tt>ServiceLoader</tt>
     * (lazily).
     * @param type The type, which should be the same as the class name in the 
     *             <tt>greenmirror.fxwrappers</tt> package, appended with <tt>FxWrapper</tt>.
     *             The first letter will be capitalized.
     * @return     The new instance.
     * @throws IllegalArgumentException If the passed type is invalid.
     */
    //@ requires type != null;
    public static FxWrapper getNewInstance(String type) {
        
        if (getPrototypes() == null) {
            prototypes = new HashSet<FxWrapper>();
            for (FxWrapper fxWrapper : ServiceLoader.load(FxWrapper.class)) {
                getPrototypes().add(fxWrapper);
            }
        }
        
        String simpleClassName = Character.toUpperCase(type.charAt(0)) + type.substring(1)
                + "FxWrapper";
        
        for (FxWrapper fxWrapperPrototype : getPrototypes()) {
            if (simpleClassName.equals(fxWrapperPrototype.getClass().getSimpleName())) {
                return fxWrapperPrototype.clone();
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
    public abstract FxWrapper clone();
    
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
        FxWrapper newValues = this.clone();
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
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)
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
     * A <tt>Transition</tt> class that animates the change in opacity. The default 
     * <tt>FadeTransition</tt> class isn't used because it's buggy when playing back 
     * transitions.
     * 
     * @author Karim El Assal
     */
    public static class FadeTransition extends DoublePropertyTransition<javafx.scene.Node> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)
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
