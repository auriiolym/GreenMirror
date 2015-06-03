package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxShapeWrapper;
import greenmirror.FxWrapper;
import greenmirror.GreenMirrorUtils;
import greenmirror.Placement;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.placements.EdgePlacement;
import greenmirror.server.DoublePropertyTransition;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.shape.Circle;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public class CircleFxWrapper extends FxShapeWrapper {
    
    // -- Enumerations -----------------------------------------------------------------------

    // -- Exceptions -------------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    private Double centerX;
    private Double centerY;
    private Double radius;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getChangableProperties()
     */
    @Override
    protected List<FxPropertyWrapper> getAnimatableProperties() {
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
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getChangableProperties()
     */
    @Override
    protected List<FxPropertyWrapper> getChangableProperties() {
        final List<FxPropertyWrapper> supersChangableProperties = super.getChangableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersChangableProperties);
                addAll(getAnimatableProperties());
            }
        };
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getFxNode()
     */
    @Override
    /*@ pure */ public javafx.scene.shape.Circle getFxNode() {
        return (javafx.scene.shape.Circle) super.getFxNode();
    }
    
    /*@ pure */ public Double getCenterX() {
        return this.centerX;
    }
    
    // Only added for support in Groovy scripts.
    /*@ pure */ public Double getX() {
        return getCenterX();
    }
    
    /*@ pure */ public Double getCenterY() {
        return this.centerY;
    }
    
    // Only added for support in Groovy scripts.
    /*@ pure */ public Double getY() {
        return getCenterY();
    }
    
    /*@ pure */ public Double getRadius() {
        return this.radius;
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#isPositionSet()
     */
    @Override
    /*@ pure */ public boolean isPositionSet() {
        return getCenterX() != null && getCenterY() != null;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    public CircleFxWrapper setCenterX(double value) {
        this.centerX = value;
        setChanged();
        notifyObservers();
        return this;
    }

    // Only used for extra support in Groovy scripts.
    public CircleFxWrapper setX(double value) {
        return setCenterX(value);
    }
    
    public CircleFxWrapper setCenterY(double value) {
        this.centerY = value;
        setChanged();
        notifyObservers();
        return this;
    }

    // Only used for extra support in Groovy scripts.
    public CircleFxWrapper setY(double value) {
        return setCenterY(value);
    }
    
    public CircleFxWrapper setPosition(double posX, double posY) {
        this.centerX = posX;
        this.centerY = posY;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public CircleFxWrapper setRadius(double value) {
        this.radius = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public CircleFxWrapper setDiameter(double value) {
        return setRadius(value / 2);
    }

    public Transition animateCenterX(double value, Duration duration) {
        return new CenterXTransition(duration, getFxNode(), value);
    }
    
    public Transition animateCenterY(double value, Duration duration) {
        return new CenterYTransition(duration, getFxNode(), value);
    }
    
    public Transition animateRadius(double value, Duration duration) {
        return new RadiusTransition(duration, getFxNode(), value);
    }
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    @Override
    public CircleFxWrapper clone() {
        CircleFxWrapper rect = new CircleFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    // -- Network responses ------------------------------------------------------------------
    
    // -- Network requests -------------------------------------------------------------------
    
    // -- View requests ----------------------------------------------------------------------
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculatePosition(greenmirror.Placement)
     */
    @Override
    public Point3D calculatePoint(Placement placement) {
        
        final double radius = getRadius();

        double calcX = 0;
        double calcY = 0;
        Double degrees = Double.NaN;
        
        switch (placement.toString()) {
        case "None": default:
            return Point3D.ZERO;
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
        
        return new Point3D(getCenterX(), getCenterY(), 0)
          .add(new Point3D(calcX, calcY, 0)
          .add(placement.getRelativePosition()));
    }
    


    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#createFxNode()
     */
    @Override
    public void createFxNode() {
        setFxNode(new Circle());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#animateToWithMiddlePoint(javafx.geometry.Point3D, 
     *                              javafx.util.Duration)
     */
    @Override
    public Transition animateToMiddlePoint(Point3D position, Duration duration) {
        return new ParallelTransition(
                new CenterXTransition(duration, getFxNode(), position.getX()),
                new CenterYTransition(duration, getFxNode(), position.getY()));
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculateCoordinates(javafx.geometry.Point3D)
     */
    @Override
    protected Point3D calculateOriginCoordinates(Point3D middlePoint) {
        return new Point3D(middlePoint.getX(), 
                           middlePoint.getY(), 0);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateOriginCoordinates(middlePoint);
        setCenterX(coord.getX());
        setCenterY(coord.getY());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setFxToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setFxToPositionWithMiddlePoint(Point3D middlePoint) {
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
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected CenterXTransition(Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getCenterX();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setCenterX(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the centerY value of a <code>Circle</code>.
     * 
     * @author Karim El Assal
     */
    public static class CenterYTransition extends DoublePropertyTransition<Circle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected CenterYTransition(Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getCenterY();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setCenterY(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the radius.
     * 
     * @author Karim El Assal
     */
    public static class RadiusTransition extends DoublePropertyTransition<Circle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected RadiusTransition(Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getRadius();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setRadius(value);
        }
    }

}
