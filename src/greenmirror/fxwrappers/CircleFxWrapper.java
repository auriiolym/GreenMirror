package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxShapeWrapper;
import greenmirror.GreenMirrorUtils;
import greenmirror.Placement;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.placements.EdgePlacement;
import greenmirror.server.DoublePropertyTransition;
import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.shape.Circle;
import javafx.util.Duration;


/**
 * The {@link greenmirror.FxWrapper} for circle FX nodes.
 * 
 * @author Karim El Assal
 */
public class CircleFxWrapper extends FxShapeWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the virtual centerX value of the FX node */
    private Double centerX;
    
    /** the virtual centerY value of the FX node */
    private Double centerY;
    
    /** the virtual radius value of the FX node */
    private Double radius;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull /*@ pure */ protected List<FxPropertyWrapper> getAnimatableProperties() {
        final List<FxPropertyWrapper> supersAnimatableProperties = super.getAnimatableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersAnimatableProperties);
                add(new DoubleFxProperty("centerX"));
                add(new DoubleFxProperty("centerY"));
                add(new DoubleFxProperty("radius"));
            }
        };
    }

    @Override @NonNull /*@ pure */ protected List<FxPropertyWrapper> getChangableProperties() {
        final List<FxPropertyWrapper> supersChangableProperties = super.getChangableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersChangableProperties);
                addAll(getAnimatableProperties());
            }
        };
    }
    
    @Override
    /*@ pure */ public javafx.scene.shape.Circle getFxNode() {
        return (javafx.scene.shape.Circle) super.getFxNode();
    }
    
    /** @return the virtual centerX value of the FX node */
    /*@ pure */ public Double getCenterX() {
        return this.centerX;
    }
    
    /** @return the virtual centerY value of the FX node */
    /*@ pure */ public Double getCenterY() {
        return this.centerY;
    }
    
    @Override
    /*@ pure */ public Double getX() {
        return getCenterX();
    }

    @Override
    /*@ pure */ public Double getY() {
        return getCenterY();
    }
    
    /** @return the virtual radius value of the FX node */
    /*@ pure */ public Double getRadius() {
        return this.radius;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * Sets the virtual centerX property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getCenterX() == value;
    @NonNull public CircleFxWrapper setCenterX(double value) {
        this.centerX = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual centerY property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getCenterY() == value;
    @NonNull public CircleFxWrapper setCenterY(double value) {
        this.centerY = value;
        setChanged();
        notifyObservers();
        return this;
    }

    @Override @NonNull
    public CircleFxWrapper setX(double value) {
        return setCenterX(value);
    }

    @Override @NonNull
    public CircleFxWrapper setY(double value) {
        return setCenterY(value);
    }
    
    @Override @NonNull
    public CircleFxWrapper setPosition(double posX, double posY) {
        this.centerX = posX;
        this.centerY = posY;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual radius property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     * @throws IllegalArgumentException if <code>value</code> is negative
     */
    //@ requires value >= 0;
    //@ ensures getRadius() == value;
    @NonNull public CircleFxWrapper setRadius(double value) {
        if (value < 0) {
            throw new IllegalArgumentException("radius can't be negative");
        }
        this.radius = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual radius (=diameter/2) property and notifies the observers.
     * 
     * @param value the new diameter value
     * @return      <code>this</code>
     */
    //@ ensures getRadius() == value / 2;
    @NonNull public CircleFxWrapper setDiameter(double value) {
        return setRadius(value / 2);
    }

    /**
     * Creates the animation that changes the centerX property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            CenterXTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateCenterX(double value, 
                                                                @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new CenterXTransition(duration, getFxNode(), value);
    }

    /**
     * Creates the animation that changes the CenterY property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if <code>value</code> is invalid
     * @see            CenterYTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateCenterY(double value, 
                                                                @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new CenterYTransition(duration, getFxNode(), value);
    }

    /**
     * Creates the animation that changes the radius property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if <code>value</code> is invalid
     * @see            RadiusTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateRadius(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new RadiusTransition(duration, getFxNode(), value);
    }
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    @Override @NonNull public CircleFxWrapper clone() {
        CircleFxWrapper circ = new CircleFxWrapper();
        circ.setFromMap(this.toMap());
        return circ;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override @NonNull 
    public Point3D calculatePoint(@NonNull Placement placement) {
        
        final double radius = getRadius();

        double calcX = 0;
        double calcY = 0;
        Double degrees = Double.NaN;
        
        switch (placement.toString()) {
        case "None": default:
            return new Point3D(0, 0, 0);
        case "Random":
            final double yRad = GreenMirrorUtils.getRandomBetween(-0.5 * Math.PI, 0.5 * Math.PI);
            final double xRadLimit = Math.cos(yRad);
            final double xRad = GreenMirrorUtils.getRandomBetween(-1 * xRadLimit, xRadLimit);

            calcX = xRad * 2 / Math.PI * radius;
            calcY = yRad * 2 / Math.PI * radius;
            break;
        case "Custom": case "Middle":
            break;
        case "Edge":
            degrees = ((EdgePlacement) placement).getAngle();
            break;
        case "EdgeTop":
            calcY = -1 * radius;
            break;
        case "EdgeRight":
            calcX = radius;
            break;
        case "EdgeBottom":
            calcY = radius;
            break;
        case "EdgeLeft":
            calcX = -1 * radius;
            break;
        case "CornerTopLeft":
            degrees = -45.0;
            break;
        case "CornerTopRight":
            degrees = 45.0;
            break;
        case "CornerBottomRight":
            degrees = 135.0;
            break;
        case "CornerBottomLeft":
            degrees = -135.0;
            break;
        }
        
        if (!Double.isNaN(degrees)) {
            final double angle = Math.toRadians(degrees);
            calcX = Math.sin(angle) * radius;
            calcY = Math.cos(angle) * radius * -1; // because positive on the canvas means down.
        }

        final Point3D returnPoint = new Point3D(getCenterX(), getCenterY(), 0)
                                                .add(new Point3D(calcX, calcY, 0)
                                                .add(placement.getRelativePosition()));
        if (returnPoint == null) {
            throw new RuntimeException("Point3D#add(Point3D) returned null");
        }
        return returnPoint;
    }
    
    @Override
    public void createFxNode() {
        setFxNode(new Circle());
    }

    @Override @NonNull 
    public Transition animateToMiddlePoint(@NonNull Point3D position, @NonNull Duration duration) {
        
        return new ParallelTransition(
                new CenterXTransition(duration, getFxNode(), position.getX()),
                new CenterYTransition(duration, getFxNode(), position.getY()));
    }
    
    @Override @NonNull 
    protected Point3D calculateOriginCoordinates(@NonNull Point3D middlePoint) {
        return new Point3D(middlePoint.getX(), 
                           middlePoint.getY(), 0);
    }

    @Override
    public void setToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        Point3D coord = calculateOriginCoordinates(middlePoint);
        setCenterX(coord.getX());
        setCenterY(coord.getY());
    }

    @Override
    public void setFxToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        Point3D coord = calculateOriginCoordinates(middlePoint);
        getFxNode().setCenterX(coord.getX());
        getFxNode().setCenterY(coord.getY());
    }


    /**
     * A <code>Transition</code> class that animates the centerX value of a <code>Circle</code>.
     * 
     * @author Karim El Assal
     */
    public static class CenterXTransition extends DoublePropertyTransition<Circle> {
        
        protected CenterXTransition(@NonNull Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getCenterX();
        }

        @Override 
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setCenterX(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the centerY value of a <code>Circle</code>.
     * 
     * @author Karim El Assal
     */
    public static class CenterYTransition extends DoublePropertyTransition<Circle> {
        
        protected CenterYTransition(@NonNull Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override 
        protected Double getPropertyValue() {
            return getNode().getCenterY();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setCenterY(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the radius.
     * 
     * @author Karim El Assal
     */
    public static class RadiusTransition extends DoublePropertyTransition<Circle> {

        protected RadiusTransition(@NonNull Duration duration, Circle node, 
                                                               @NonNull Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getRadius();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setRadius(value);
        }
    }

}
