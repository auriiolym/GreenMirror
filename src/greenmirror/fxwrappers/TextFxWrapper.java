package greenmirror.fxwrappers;

import greenmirror.FxShapeWrapper;
import greenmirror.FxWrapper;
import greenmirror.Placement;
import greenmirror.fxpropertytypes.DoubleFxProperty;
import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.fxpropertytypes.StringFxProperty;
import greenmirror.server.AbstractTransition;
import greenmirror.server.DoublePropertyTransition;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.geometry.VPos;
import javafx.scene.text.Text;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public class TextFxWrapper extends FxShapeWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    private Double posX;
    private Double posY;
    private Double wrappingWidth;
    private String text;
    

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
                add(new DoubleFxProperty("wrappingWidth"));
                add(new StringFxProperty("text"));
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
    /*@ pure */ public javafx.scene.text.Text getFxNode() {
        return (javafx.scene.text.Text) super.getFxNode();
    }
    
    

    /**
     * @return The x coordinate.
     */
    /*@ pure */ public Double getX() {
        return posX;
    }

    /**
     * @return The y coordinate.
     */
    /*@ pure */ public Double getY() {
        return posY;
    }

    /**
     * @return The wrappingWidth.
     */
    /*@ pure */ public Double getWrappingWidth() {
        return wrappingWidth;
    }

    /**
     * @return The text.
     */
    /*@ pure */ public String getText() {
        return text;
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#isPositionSet()
     */
    @Override
    /*@ pure */ public boolean isPositionSet() {
        return getX() != null && getY() != null;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param value The posX to set.
     */
    //@ ensures getX().doubleValue() == value;
    //@ ensures \result == this;
    public TextFxWrapper setX(double value) {
        this.posX = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param value The posY to set.
     */
    //@ ensures getY().doubleValue() == value;
    //@ ensures \result == this;
    public TextFxWrapper setY(double value) {
        this.posY = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * @param posX The posX to set.
     * @param posY The posY to set.
     * @return     <tt>this</tt>
     */
    //@ ensures getX().doubleValue() == posX && getY().doubleValue() == posY;
    //@ ensures \result == this;
    public TextFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param value The image to set.
     */
    //@ ensures getText() == value;
    //@ ensures \result == this;
    public TextFxWrapper setText(String value) {
        this.text = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param wrappingWidth The fitWidth to set.
     */
    //@ ensures getWrappingWidth().doubleValue() == value;
    //@ ensures \result == this;
    public TextFxWrapper setWrappingWidth(double wrappingWidth) {
        this.wrappingWidth = wrappingWidth;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public Transition animateX(double value, Duration duration) {
        return new XTransition(duration, getFxNode(), value);
    }
    
    public Transition animateY(double value, Duration duration) {
        return new YTransition(duration, getFxNode(), value);
    }
    
    public Transition animateWrappingWidth(double value, Duration duration) {
        return new WrappingWidthTransition(duration, getFxNode(), value);
    }
    
    public Transition animateText(String value, Duration duration) {
        return new TextTransition(duration, getFxNode(), value);
    }
    

    // -- Class usage ------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#clone()
     */
    @Override
    public TextFxWrapper clone() {
        TextFxWrapper rect = new TextFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculatePoint(greenmirror.Placement)
     */
    @Override
    /*@ pure */ public Point3D calculatePoint(Placement placement) {
        double width = getWrappingWidth() == null ? 0 : getWrappingWidth();
        double height = 0;
        /*
        if (getFxNode() != null) {
            width = getFxNode().getBoundsInLocal().getWidth();
            height = getFxNode().getBoundsInLocal().getHeight();
        }*/
        return new Point3D(getX(), getY(), 0)
            .add(FxWrapper.calculatePointOnRectangle(width, height, placement));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#createFxNode()
     */
    @Override
    public void createFxNode() {
        final Text node = new Text();
        node.setTextOrigin(VPos.TOP);
        setFxNode(node);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#animateToMiddlePoint(javafx.geometry.Point3D, 
     *                                          javafx.util.Duration)
     */
    @Override
    public Transition animateToMiddlePoint(Point3D middlePoint, Duration duration) {
        Point3D coord = calculateCoordinates(middlePoint);
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), coord.getX()),
                new YTransition(duration, getFxNode(), coord.getY()));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculateCoordinates(javafx.geometry.Point3D)
     */
    @Override
    protected Point3D calculateCoordinates(Point3D middlePoint) {
        return new Point3D(middlePoint.getX() - getWrappingWidth() / 2, 
                           middlePoint.getY() - 1 / 2, 0);
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
     * A <tt>Transition</tt> class that animates the x value of a <tt>Text</tt>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<Text> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected XTransition(Duration duration, Text node, Double toValue) {
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
     * A <tt>Transition</tt> class that animates the y value of a <tt>Text</tt>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<Text> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected YTransition(Duration duration, Text node, Double toValue) {
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
     * A <tt>Transition</tt> class that animates the change of the wrapping width.
     * 
     * @author Karim El Assal
     */
    public static class WrappingWidthTransition extends DoublePropertyTransition<Text> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected WrappingWidthTransition(Duration duration, Text node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getWrappingWidth();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setWrappingWidth(value);
        }
    }
    
    
    public static class TextTransition extends AbstractTransition<Text, String> {

        // --- Constructors -------------------------------
        
        public TextTransition(Duration duration, Text node, String toValue) {
            super(duration, node, toValue);
        }
        
        
        // --- Commands -----------------------------------
        
        /* (non-Javadoc)
         * @see javafx.animation.Transition#interpolate(double)
         */
        @Override
        //@ requires getNode() != null;
        protected void interpolate(final double frac) {
            if (getFromValue() == null) {
                setFromValue(getNode().getText());
            }

            final double part1Frac = frac * 2;
            final double part2Frac = (frac - 0.5) * 2;
            // First half: only change the opacity to 0.
            if (frac <= 0.5) {
                if (!getNode().getText().equals(getFromValue())) {
                    getNode().setText(getFromValue());
                }
                final double valueDiff = 0 - getOriginalOpacity();
                getNode().setOpacity(getOriginalOpacity() + valueDiff * part1Frac);
             
            // Second half: change the opacity back to the original and set the new text.
            } else {
                if (!getNode().getText().equals(getToValue())) {
                    getNode().setText(getToValue());
                }
                final Double valueDiff = getOriginalOpacity() - 0;
                getNode().setOpacity(0 + valueDiff * part2Frac);
            }
        }
    }
}
