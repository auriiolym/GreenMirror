package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxShapeWrapper;
import greenmirror.FxWrapper;
import greenmirror.GreenMirrorUtils;
import greenmirror.Placement;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.server.DoublePropertyTransition;

import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.shape.Rectangle;
import javafx.util.Duration;

/**
 * The {@link greenmirror.FxWrapper} for rectangle FX nodes.
 * 
 * @author Karim El Assal
 */
public class RectangleFxWrapper extends FxShapeWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the virtual x value of the FX node */
    private Double posX;
    
    /** the virtual y value of the FX node */
    private Double posY;
    
    /** the virtual width value of the FX node */
    private Double width;
    
    /** the virtual height value of the FX node */
    private Double height;
    
    /** the virtual arcWidth value of the FX node */
    private Double arcWidth;
    
    /** the virtual arcHeight value of the FX node */
    private Double arcHeight;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull /*@ pure */ protected List<FxPropertyWrapper> getAnimatableProperties() {
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
    /*@ pure */ public javafx.scene.shape.Rectangle getFxNode() {
        return (javafx.scene.shape.Rectangle) super.getFxNode();
    }
    
    @Override
    /*@ pure */ public Double getX() {
        return this.posX;
    }
    
    @Override
    /*@ pure */ public Double getY() {
        return this.posY;
    }
    
    /** @return the virtual width value of the FX node */
    /*@ pure */ public Double getWidth() {
        return this.width;
    }
    
    /** @return the virtual height value of the FX node */
    /*@ pure */ public Double getHeight() {
        return this.height;
    }
    
    /** @return the virtual arcWidth value of the FX node */
    /*@ pure */ public Double getArcWidth() {
        return this.arcWidth;
    }
    
    /** @return the virtual arcHeight value of the FX node */
    /*@ pure */ public Double getArcHeight() {
        return this.arcHeight;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * Sets the virtual x property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getX() == value;
    @Override @NonNull public RectangleFxWrapper setX(double value) {
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
    //@ ensures getY() == value;
    @Override @NonNull public RectangleFxWrapper setY(double value) {
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
    @Override @NonNull public RectangleFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual width property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getWidth() == value;
    @NonNull public RectangleFxWrapper setWidth(double value) {
        this.width = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual height property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getHeight() == value;
    @NonNull public RectangleFxWrapper setHeight(double value) {
        this.height = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual width and height properties and notifies the observers.
     * 
     * @param width  the new width
     * @param height the new height
     * @return       <code>this</code>
     */
    //@ ensures getWidth() == width && getHeight() == height;
    @NonNull public RectangleFxWrapper setSize(double width, double height) {
        this.width = width;
        this.height = height;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual arcWidth property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getArcWidth() == value;
    @NonNull public RectangleFxWrapper setArcWidth(double value) {
        this.arcWidth = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual arcHeight property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getArcHeight() == value;
    @NonNull public RectangleFxWrapper setArcHeight(double value) {
        this.arcHeight = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual arcWidth and arcHeight properties and notifies the observers.
     * 
     * @param width  the new arc width
     * @param height the new arc height
     * @return       <code>this</code>
     */
    //@ ensures getArcWidth() == width && getArcHeight() == height;
    @NonNull public RectangleFxWrapper setArcs(double width, double height) {
        this.arcWidth = width;
        this.arcHeight = height;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual arcWidth and arcHeight properties and notifies the observers.
     * 
     * @param value the new value for both the width and the height
     * @return      <code>this</code>
     */
    //@ ensures getArcWidth() == value && getArcHeight();
    @NonNull public RectangleFxWrapper setArcs(double value) {
        return setArcs(value, value);
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
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
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
     * Creates the animation that changes the width property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            WidthTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateWidth(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new WidthTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the height property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            HeightTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateHeight(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new HeightTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the arcWidth property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            ArcWidthTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateArcWidth(double value, 
                                                           @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new ArcWidthTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the arcHeight property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            ArcHeightTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateArcHeight(double value, 
                                                            @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new ArcHeightTransition(duration, getFxNode(), value);
    }
    
    
    // -- Class usage ------------------------------------------------------------------------
    
    @Override @NonNull 
    public RectangleFxWrapper clone() {
        RectangleFxWrapper rect = new RectangleFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override @NonNull 
    public Point3D calculatePoint(@NonNull Placement placement) {
        
        final Point3D returnPoint
            =  new Point3D(getX(), getY(), 0)
                    .add(FxWrapper.calculatePointOnRectangle(getWidth(), getHeight(), placement));
        if (returnPoint == null) {
            throw new RuntimeException("Point3D#add(Point3D) returned null");
        }
        return returnPoint;
    }
    
    @Override
    public void createFxNode() {
        setFxNode(new Rectangle());
    }

    @Override @NonNull 
    public Transition animateToMiddlePoint(@NonNull Point3D position, @NonNull Duration duration) {
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), position.getX() - getWidth() / 2),
                new YTransition(duration, getFxNode(), position.getY() - getHeight() / 2));
    }
    
    @Override @NonNull 
    protected Point3D calculateOriginCoordinates(@NonNull Point3D middlePoint) {
        return new Point3D(middlePoint.getX() - getWidth() / 2, 
                           middlePoint.getY() - getHeight() / 2, 0);
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
     * A <code>Transition</code> class that animates the x value of a <code>Rectangle</code>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<Rectangle> {
        
        protected XTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
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
     * A <code>Transition</code> class that animates the y value of a <code>Rectangle</code>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<Rectangle> {
        
        protected YTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
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
     * A <code>Transition</code> class that animates the change of the width.
     * 
     * @author Karim El Assal
     */
    public static class WidthTransition extends DoublePropertyTransition<Rectangle> {

        protected WidthTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getWidth();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setWidth(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the height.
     * 
     * @author Karim El Assal
     */
    public static class HeightTransition extends DoublePropertyTransition<Rectangle> {

        protected HeightTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getHeight();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setHeight(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the arc width.
     * 
     * @author Karim El Assal
     */
    public static class ArcWidthTransition extends DoublePropertyTransition<Rectangle> {
        
        protected ArcWidthTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getArcWidth();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setArcWidth(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the arc height.
     * 
     * @author Karim El Assal
     */
    public static class ArcHeightTransition extends DoublePropertyTransition<Rectangle> {
        
        protected ArcHeightTransition(@NonNull Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getArcHeight();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setArcHeight(value);
        }
    }

}
