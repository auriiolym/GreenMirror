package greenmirror.server;

import greenmirror.VisualComponent;

import javafx.animation.Transition;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public abstract class DoublePropertyTransition<E extends javafx.scene.Node & VisualComponent>
    extends Transition {

    // --- Instance variables ----------------------------------------------------------------

    private Double fromValue;
    
    private Double toValue;
    
    private E node;
    
    
    // --- Constructors ----------------------------------------------------------------------
    public void DoubleePropertyTransition(Duration duration, E node, Double toValue) {
        
    }
    public DoublePropertyTransition(Duration duration, E node, Double toValue) {
        setDuration(duration);
        setNode(node);
        setToValue(toValue);
    }
    
    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return The fromValue.
     */
    /*@ pure */ public Double getFromValue() {
        return fromValue;
    }

    /**
     * @return The toValue.
     */
    /*@ pure */ public Double getToValue() {
        return toValue;
    }

    /**
     * @return The node.
     */
    /*@ pure */ public E getNode() {
        return node;
    }

    /**
     * @return The duration.
     */
    /*@ pure */ public Duration getDuration() {
        return this.getCycleDuration();
    }
    
    
    // --- Setters ---------------------------------------------------------------------------

    /**
     * @param fromValue The fromValue to set.
     */
    public void setFromValue(Double fromValue) {
        this.fromValue = fromValue;
    }

    /**
     * @param toValue The toValue to set.
     */
    public void setToValue(Double toValue) {
        this.toValue = toValue;
    }

    /**
     * @param node The node to set.
     */
    public void setNode(E node) {
        this.node = node;
    }

    /**
     * @param duration The duration to set.
     */
    public void setDuration(Duration duration) {
        this.setCycleDuration(duration);
    }

    
    // --- Commands --------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see javafx.animation.Transition#interpolate(double)
     */
    @Override
    //@ requires getNode() != null;
    protected void interpolate(double frac) {
        if (getFromValue() == null) {
            setFromValue(getPropertyValue());
        }
        
        final Double valueDiff = getToValue() - getFromValue();
        setPropertyValue(getFromValue() + valueDiff * frac);
    }
    
    protected abstract Double getPropertyValue();
    
    protected abstract void setPropertyValue(Double value);
    
}
