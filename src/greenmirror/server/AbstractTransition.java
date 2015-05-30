package greenmirror.server;

import javafx.animation.Transition;
import javafx.util.Duration;

/**
 * A general Transition class.
 * 
 * @author Karim El Assal
 */
public abstract class AbstractTransition<E extends javafx.scene.Node, T extends Object>
    extends Transition {

    // --- Instance variables ----------------------------------------------------------------

    private T fromValue;
    
    private T toValue;
    
    private E node;

    private Double originalOpacity;
    
    
    // --- Constructors ----------------------------------------------------------------------
    
    public AbstractTransition(Duration duration, E node, T toValue) {
        setDuration(duration);
        setNode(node);
        setToValue(toValue);
    }
    
    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return The fromValue.
     */
    /*@ pure */ public T getFromValue() {
        return fromValue;
    }

    /**
     * @return The toValue.
     */
    /*@ pure */ public T getToValue() {
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
    
    /**
     * @return The node's originalOpacity.
     */
    public double getOriginalOpacity() {
        if (originalOpacity == null) {
            originalOpacity = getNode().getOpacity();
        }
        return originalOpacity;
    }
    
    
    // --- Setters ---------------------------------------------------------------------------

    /**
     * @param fromValue The fromValue to set.
     */
    public void setFromValue(T fromValue) {
        this.fromValue = fromValue;
    }

    /**
     * @param toValue The toValue to set.
     */
    public void setToValue(T toValue) {
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
    protected abstract void interpolate(double frac);
    
}
