package greenmirror.fxwrappers;

import greenmirror.FxShapeWrapper;
import greenmirror.Placement;
import greenmirror.fxpropertytypes.DoubleFxProperty;
import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.server.DoublePropertyTransition;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.paint.Paint;
import javafx.scene.shape.Rectangle;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public class RectangleFxWrapper extends FxShapeWrapper {
    
    // -- Enumerations -----------------------------------------------------------------------

    // -- Exceptions -------------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    private Double posX;
    private Double posY;
    private Double width;
    private Double height;
    private Double arcWidth;
    private Double arcHeight;

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
                add(new DoubleFxProperty("x"));
                add(new DoubleFxProperty("y"));
                add(new DoubleFxProperty("width"));
                add(new DoubleFxProperty("height"));
                add(new DoubleFxProperty("arcWidth"));
                add(new DoubleFxProperty("arcHeight"));
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
    
    /*@ pure */ public javafx.scene.shape.Rectangle getFxNode() {
        return (javafx.scene.shape.Rectangle) super.getFxNode();
    }
    
    /*@ pure */ public Double getX() {
        return this.posX;
    }
    
    /*@ pure */ public Double getY() {
        return this.posY;
    }
    
    /*@ pure */ public Double getWidth() {
        return this.width;
    }
    
    /*@ pure */ public Double getHeight() {
        return this.height;
    }
    
    /*@ pure */ public Double getArcWidth() {
        return this.arcWidth;
    }
    
    /*@ pure */ public Double getArcHeight() {
        return this.arcHeight;
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#isPositionSet()
     */
    @Override
    /*@ pure */ public boolean isPositionSet() {
        return getX() != null && getY() != null;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    public RectangleFxWrapper setX(double value) {
        this.posX = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setY(double value) {
        this.posY = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setWidth(double value) {
        this.width = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setHeight(double value) {
        this.height = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setSize(double width, double height) {
        this.width = width;
        this.height = height;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setArcWidth(double value) {
        this.arcWidth = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setArcHeight(double value) {
        this.arcHeight = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setArcs(double width, double height) {
        this.arcWidth = width;
        this.arcHeight = height;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public RectangleFxWrapper setArcs(double value) {
        return setArcs(value, value);
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxShapeWrapper#setFill(javafx.scene.paint.Paint)
     */
    @Override
    public RectangleFxWrapper setFill(Paint value) {
        return (RectangleFxWrapper) super.setFill(value);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxShapeWrapper#setFill(java.lang.String)
     */
    @Override
    public RectangleFxWrapper setFill(String value) {
        return (RectangleFxWrapper) super.setFill(value);
    }

    public Transition animateX(double value, Duration duration) {
        return new XTransition(duration, getFxNode(), value);
    }
    
    public Transition animateY(double value, Duration duration) {
        return new YTransition(duration, getFxNode(), value);
    }
    
    public Transition animateWidth(double value, Duration duration) {
        return new WidthTransition(duration, getFxNode(), value);
    }
    
    public Transition animateHeight(double value, Duration duration) {
        return new HeightTransition(duration, getFxNode(), value);
    }
    
    public Transition animateArcWidth(double value, Duration duration) {
        return new ArcWidthTransition(duration, getFxNode(), value);
    }
    
    public Transition animateArcHeight(double value, Duration duration) {
        return new ArcHeightTransition(duration, getFxNode(), value);
    }
    
    // -- Class usage ------------------------------------------------------------------------
    
    @Override
    public RectangleFxWrapper clone() {
        RectangleFxWrapper rect = new RectangleFxWrapper();
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
        double posX;
        double posY;
        
        switch (placement.toString()) {
        case "None": default:
            return null;
        case "Random":
            Random random = new Random();
            double minX = getX();
            double maxX = getX() + getWidth();
            double minY = getY();
            double maxY = getY() + getHeight();

            posX = minX + random.nextDouble() * (maxX - minX);
            posY = minY + random.nextDouble() * (maxY - minY);
            break;
        case "Custom": case "Middle":
            posX = getX() + getWidth() / 2;
            posY = getY() + getHeight() / 2;
            break;
        case "EdgeTop":
            posX = getX() + getWidth() / 2;
            posY = getY();
            break;
        case "EdgeRight":
            posX = getX() + getWidth();
            posY = getY() + getHeight() / 2;
            break;
        case "EdgeBottom":
            posX = getX() + getWidth() / 2;
            posY = getY() + getHeight();
            break;
        case "EdgeLeft":
            posX = getX();
            posY = getY() + getHeight() / 2;
            break;
        case "CornerTopLeft":
            posX = getX(); 
            posY = getY();
            break;
        case "CornerTopRight":
            posX = getX() + getWidth();
            posY = getY();
            break;
        case "CornerBottomRight":
            posX = getX() + getWidth();
            posY = getY() + getHeight();
            break;
        case "CornerBottomLeft":
            posX = getX();
            posY = getY() + getHeight();
            break;
        }
        return new Point3D(posX, posY, 0).add(placement.getRelativePosition());
    }
    


    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#createFxNode()
     */
    @Override
    public void createFxNode() {
        setFxNode(new Rectangle());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#animateToPositionWithMiddlePoint(javafx.geometry.Point3D, 
     *                              javafx.util.Duration)
     */
    @Override
    public Transition animateToMiddlePoint(Point3D position, Duration duration) {
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), position.getX() - getWidth() / 2),
                new YTransition(duration, getFxNode(), position.getY() - getHeight() / 2));
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculateCoordinates(javafx.geometry.Point3D)
     */
    @Override
    protected Point3D calculateCoordinates(Point3D middlePoint) {
        return new Point3D(middlePoint.getX() - getWidth() / 2, 
                           middlePoint.getY() - getHeight() / 2, 0);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateCoordinates(middlePoint);
        setX(coord.getX());
        setY(coord.getY());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setFxToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setFxToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateCoordinates(middlePoint);
        getFxNode().setX(coord.getX());
        getFxNode().setY(coord.getY());
    }


    /**
     * A <tt>Transition</tt> class that animates the x value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected XTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getX();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setX(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the y value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected YTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getY();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setY(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the width.
     * 
     * @author Karim El Assal
     */
    public static class WidthTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected WidthTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getWidth();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setWidth(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the height.
     * 
     * @author Karim El Assal
     */
    public static class HeightTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected HeightTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getHeight();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setHeight(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the arc width.
     * 
     * @author Karim El Assal
     */
    public static class ArcWidthTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected ArcWidthTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getArcWidth();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setArcWidth(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the arc height.
     * 
     * @author Karim El Assal
     */
    public static class ArcHeightTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected ArcHeightTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getArcHeight();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setArcHeight(value);
        }
    }

}
