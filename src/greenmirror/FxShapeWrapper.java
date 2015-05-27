package greenmirror;

import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.fxpropertytypes.PaintFxProperty;

import java.util.ArrayList;
import java.util.List;

import javafx.animation.FillTransition;
import javafx.animation.Transition;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public abstract class FxShapeWrapper extends FxWrapper {

    // -- Enumerations -----------------------------------------------------------------------

    // -- Exceptions -------------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    private Paint fill;

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
    /*@ pure */ public javafx.scene.shape.Shape getFxNode() {
        return (javafx.scene.shape.Shape) super.getFxNode();
    }
    
    /*@ pure */ public Paint getFill() {
        return this.fill;
    }
    
    // -- Setters ----------------------------------------------------------------------------
    

    public FxShapeWrapper setFill(Paint value) {
        this.fill = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    public FxShapeWrapper setFill(String value) {
        return setFill(Paint.valueOf(value));
    }
    
    public Transition animateFill(Paint value, Duration duration) {
        return animateFill(Color.valueOf(value.toString()), duration);
    }
    
    public Transition animateFill(Color value, Duration duration) {
        FillTransition transition = new FillTransition(duration, getFxNode());
        transition.setToValue(value);
        return transition;
    }
    
    public Transition animateFill(String value, Duration duration) {
        return animateFill(Color.valueOf(value), duration);
    }
    
    // -- Class usage ------------------------------------------------------------------------
    
    // -- Network responses ------------------------------------------------------------------
    
    // -- Network requests -------------------------------------------------------------------
    
    // -- View requests ----------------------------------------------------------------------
    
    // -- Commands ---------------------------------------------------------------------------
    
}
