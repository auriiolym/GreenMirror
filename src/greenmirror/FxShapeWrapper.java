package greenmirror;

import greenmirror.fxpropertywrappers.PaintFxProperty;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.FillTransition;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.scene.shape.Shape;
import javafx.util.Duration;

/**
 * A small extension of the {@link greenmirror.FxWrapper} class. It's meant to wrap Java FX
 * nodes that are an instance of {@link javafx.scene.shape.Shape}.
 * <p>
 * All JavaFX <code>Shape</code> nodes have a fill property, so this class adds it to the
 * wrapper functionalities it inherits from <code>FxWrapper</code>.
 * 
 * @author Karim El Assal
 * @see    greenmirror.FxWrapper
 * @see    javafx.scene.shape.Shape
 */
public abstract class FxShapeWrapper extends FxWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the virtual fill property */
    private Paint fill = Color.BLACK;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getAnimatableProperties()
     */
    @Override
    protected List<FxPropertyWrapper> getAnimatableProperties() {
        final List<FxPropertyWrapper> supersAnimatableProperties = super.getAnimatableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersAnimatableProperties);
                add(new PaintFxProperty("fill"));
                //TODO: add animatable stroke properties.
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
                //TODO: add all stroke properties.
            }
        };
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getFxNode()
     */
    @Override
    public Shape getFxNode() {
        return (Shape) super.getFxNode();
    }
    
    /**
     * @return the virtual fill property value
     */
    /*@ pure */ public Paint getFill() {
        return this.fill;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * Sets the virtual fill of the JavaFX node and notifies the observer (the 
     * GreenMirror node, if this <code>FxShapeWrapper</code> is part of a GreenMirror node). 
     * 
     * @param value the new fill
     * @return      <code>this</code>
     * @see         javafx.scene.shape.Shape#setFill(Paint)
     */
    //@ ensures getFill() == value;
    //@ ensures \result == this;
    /*@ non_null */ public FxShapeWrapper setFill(Paint value) {
        this.fill = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual fill of the JavaFX node and notifies the observer (the 
     * GreenMirror node, if this <code>FxShapeWrapper</code> is part of a GreenMirror node). 
     * It uses <code>Paint.valueOf(value)</code> to get the <code>Paint</code> value.
     * <p>
     * Note that <code>value</code> should result in a <code>Color</code> type if the setting
     * of the fill property will result in an animation: anything other than the
     * <code>Color</code> subtype of <code>Paint</code> can <b>not</b> be animated. 
     * 
     * @param value the new fill
     * @return      <code>this</code>
     * @throws NullPointerException     if <code>value</code> is <code>null</code>
     * @throws IllegalArgumentException if <code>value</code> can not be parsed by the
     *                                  <code>Paint.valueOf(String)</code> method
     * @see         #setFill(Paint)
     * @see         javafx.scene.shape.Shape#setFill(Paint)
     */
    //@ ensures getFill() == value;
    //@ ensures \result == this;
    /*@ non_null */ public FxShapeWrapper setFill(/*@ non_null */ String value) {
        if (value == null) {
            throw new NullPointerException("fill value" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        return setFill(Paint.valueOf(value));
    }
    
    /**
     * Creates the animation that changes the fill property of the JavaFX node to 
     * <code>value</code>. 
     * <p>
     * <code>value</code> is first converted to type <code>Color</code> using
     * <code>Color.valueOf(value.toString())</code>. There are some important remarks 
     * about why this is done to <code>value</code> available 
     * {{@link #animateFill(Color, Duration) here}.
     * 
     * @param value    the fill value to change to
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if the 'to' or 'from' value can't be animated
     * @throws         NullPointerException     if <code>value</code> or <code>duration</code> is 
     *                                          <code>null</code>
     * @see            #animateFill(Color, Duration)
     * @see            FillTransition
     * @see            Color
     * @see            Color#valueOf(String)
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue().equals(value) && \result.getDuration() == duration;
    //@ ensures \result.getShape() == getFxNode();
    /*@ pure non_null*/ public FillTransition animateFill(/*@ non_null */ Paint value,
            /*@ non_null */ Duration duration) {
        return animateFill(Color.valueOf(value.toString()), duration);
    }
    
    /**
     * Creates the animation that changes the fill property of the JavaFX node to 
     * <code>value</code>.
     * <p>
     * There are some important remarks about <code>value</code> available
     * {{@link #animateFill(Color, Duration) here}.
     * 
     * @param value    the fill value to change to
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if the 'to' or 'from' value can't be animated
     * @throws         NullPointerException     if <code>value</code> or <code>duration</code> is 
     *                                          <code>null</code>
     * @see            #animateFill(Color, Duration)
     * @see            FillTransition
     * @see            Color
     * @see            Color#valueOf(String)
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue().equals(value) && \result.getDuration() == duration;
    //@ ensures \result.getShape() == getFxNode();
    /*@ pure non_null*/ public FillTransition animateFill(String value, Duration duration) {
        return animateFill(Color.valueOf(value), duration);
    }
    
    /**
     * Creates the animation that changes the fill property of the JavaFX node to 
     * <code>value</code>.
     * <p>
     * When animating a fill change, the 'from' and 'to' fill values <b>must</b> be of the
     * {@link Paint} subtype {@link Color}. Any other subtypes can <b>not</b> be animated. 
     * If one tries to use any other <code>Paint</code> subtype for an animation, a 
     * <code>IllegalArgumentException</code> is thrown by the
     * {@link Color#valueOf(String) Color.valueOf(String)} method.
     * 
     * @param value    the fill value to change to
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @throws         IllegalArgumentException if the 'to' or 'from' value can't be animated
     * @throws         NullPointerException     if <code>value</code> or <code>duration</code> is 
     *                                          <code>null</code>
     * @see            FillTransition
     * @see            Color
     * @see            Color#valueOf(String)
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue().equals(value) && \result.getDuration() == duration;
    //@ ensures \result.getShape() == getFxNode();
    /*@ pure non_null*/ public FillTransition animateFill(/*@ non_null */ Color value, 
            /*@ non_null */ Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        if (value == null || duration == null) {
            throw new NullPointerException("fill value and duration" 
                    + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        final FillTransition transition = new FillTransition(duration, getFxNode());
        transition.setFromValue(getFill() == null 
                ? Color.BLACK : Color.valueOf(getFill().toString()));
        transition.setToValue(value);
        return transition;
    }
    
}
