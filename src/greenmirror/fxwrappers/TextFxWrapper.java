package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxShapeWrapper;
import greenmirror.FxWrapper;
import greenmirror.GreenMirrorUtils;
import greenmirror.Placement;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.fxpropertywrappers.StringFxProperty;
import greenmirror.server.AbstractTransition;
import greenmirror.server.DoublePropertyTransition;
import org.eclipse.jdt.annotation.NonNull;

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

    /** the virtual x value of the FX node */
    private Double posX;
    /** the virtual y value of the FX node */
    private Double posY;
    /** the virtual wrappingWidth value of the FX node */
    private Double wrappingWidth;
    /** the virtual text value of the FX node */
    private String text;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    
    @Override @NonNull
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
    
    @Override @NonNull
    protected List<FxPropertyWrapper> getChangableProperties() {
        final List<FxPropertyWrapper> supersChangableProperties = super.getChangableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersChangableProperties);
                addAll(getAnimatableProperties());
            }
        };
    }
    
    @Override
    /*@ pure */ public javafx.scene.text.Text getFxNode() {
        return (javafx.scene.text.Text) super.getFxNode();
    }
    
    

    @Override
    /*@ pure */ public Double getX() {
        return posX;
    }

    @Override
    /*@ pure */ public Double getY() {
        return posY;
    }

    /** @return the virtual wrappingWidth value of the FX node */
    /*@ pure */ public Double getWrappingWidth() {
        return wrappingWidth;
    }

    /** @return the virtual text value of the FX node */
    /*@ pure */ public String getText() {
        return text;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * Sets the virtual x property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getX() == value;
    @Override @NonNull public TextFxWrapper setX(double value) {
        this.posX = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the virtual y property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getX() == value;
    @Override @NonNull public TextFxWrapper setY(double value) {
        this.posY = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual x and y properties and notifies the observers.
     * 
     * @param posX the x coordinate
     * @param posY the y coordinate
     * @return      <code>this</code>
     */
    //@ ensures getX() == posX && getY() == posY;
    @Override @NonNull public TextFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the virtual text property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getText() == value;
    @NonNull public TextFxWrapper setText(String value) {
        this.text = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the virtual wrappingWidth property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getWrappingWidth() == value;
    @NonNull public TextFxWrapper setWrappingWidth(double wrappingWidth) {
        this.wrappingWidth = wrappingWidth;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Creates the animation that changes the x property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @see            XTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateX(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new XTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the y property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @see            YTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateY(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new YTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the wrappingWidth property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @see            WrappingWidthTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateWrappingWidth(double value, 
                                                                @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new WrappingWidthTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the text property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @see            TextTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateText(String value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new TextTransition(duration, getFxNode(), value);
    }
    

    // -- Class usage ------------------------------------------------------------------------

    @Override @NonNull
    public TextFxWrapper clone() {
        TextFxWrapper rect = new TextFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override @NonNull 
    /*@ pure */ public Point3D calculatePoint(@NonNull Placement placement) {
        double width = getWrappingWidth() == null ? 0 : getWrappingWidth();
        double height = 0;

        final Point3D returnPoint
            =  new Point3D(getX(), getY(), 0)
                    .add(FxWrapper.calculatePointOnRectangle(width, height, placement));
        if (returnPoint == null) {
            throw new RuntimeException("Point3D#add(Point3D) returned null");
        }
        return returnPoint;
    }

    @Override
    public void createFxNode() {
        final Text node = new Text();
        node.setTextOrigin(VPos.TOP);
        setFxNode(node);
    }

    @Override @NonNull 
    public Transition animateToMiddlePoint(@NonNull Point3D middlePoint, 
                                           @NonNull Duration duration) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), coord.getX()),
                new YTransition(duration, getFxNode(), coord.getY()));
    }

    @Override @NonNull 
    protected Point3D calculateOriginCoordinates(@NonNull Point3D middlePoint) {
        return new Point3D(middlePoint.getX() - getWrappingWidth() / 2, 
                           middlePoint.getY() - 1 / 2, 0);
    }

    @Override
    public void setToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        setX(coord.getX());
        setY(coord.getY());
    }

    @Override
    public void setFxToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        getFxNode().setX(coord.getX());
        getFxNode().setY(coord.getY());
    }

    

    /**
     * A <code>Transition</code> class that animates the x value of a <code>Text</code>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<Text> {
        
        protected XTransition(@NonNull Duration duration, Text node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getX();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setX(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the y value of a <code>Text</code>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<Text> {
        
        protected YTransition(@NonNull Duration duration, Text node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getY();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setY(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the wrapping width.
     * 
     * @author Karim El Assal
     */
    public static class WrappingWidthTransition extends DoublePropertyTransition<Text> {
        
        protected WrappingWidthTransition(@NonNull Duration duration, Text node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getWrappingWidth();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setWrappingWidth(value);
        }
    }
    
    
    public static class TextTransition extends AbstractTransition<Text, String> {

        // --- Constructors -------------------------------
        
        public TextTransition(@NonNull Duration duration, Text node, String toValue) {
            super(duration, node, toValue);
        }
        
        
        // --- Commands -----------------------------------
        
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
