package greenmirror.server;

import org.eclipse.jdt.annotation.NonNull;

import javafx.animation.Transition;
import javafx.util.Duration;

/**
 * A {@link Transition} extension that holds features used by all subclasses. These are only
 * simple ones: getters and setters for the 'from' value (the starting value), the 'to' value
 * (the final value), the node to which the transition applies, the duration of the transition 
 * and the original opacity.
 * <p>
 * The {@link #interpolate(double)} method is the important one and has to be implemented by
 * extending classes.
 * 
 * @author Karim El Assal
 * @see Transition
 */
public abstract class AbstractTransition<E extends javafx.scene.Node, T extends Object>
    extends Transition {

    // --- Instance variables ----------------------------------------------------------------

    /** the 'from' value */
    private T fromValue;
    
    /** the 'to' value */
    private T toValue;
    
    /** the node to which the transition applies */
    private E node;

    /** the original opacity */
    private Double originalOpacity;
    
    
    // --- Constructors ----------------------------------------------------------------------
    
    /**
     * Create a new <code>AbstractTransition</code> and set the required values.
     * 
     * @param duration the duration of the transition
     * @param node     the node to which the transition applies
     * @param toValue  the 'to' value
     */
    //@ ensures getDuration() == duration && getNode() == node && getToValue() == toValue;
    public AbstractTransition(@NonNull Duration duration, E node, T toValue) {
        setDuration(duration);
        setNode(node);
        setToValue(toValue);
    }
    
    
    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return the 'from' value
     */
    /*@ pure */ public T getFromValue() {
        return fromValue;
    }

    /**
     * @return the 'to' value
     */
    /*@ pure */ public T getToValue() {
        return toValue;
    }

    /**
     * @return the node to which the transition applies
     */
    /*@ pure */ public E getNode() {
        return node;
    }

    /**
     * @return the duration of the transition
     */
    /*@ pure */ public Duration getDuration() {
        return this.getCycleDuration();
    }
    
    /**
     * @return the node's original opacity
     */
    public double getOriginalOpacity() {
        if (originalOpacity == null) {
            originalOpacity = getNode().getOpacity();
        }
        return originalOpacity;
    }
    
    
    // --- Setters ---------------------------------------------------------------------------

    /**
     * @param fromValue the 'from' value to set
     */
    public void setFromValue(T fromValue) {
        this.fromValue = fromValue;
    }

    /**
     * @param toValue the 'to' value to set
     */
    public void setToValue(T toValue) {
        this.toValue = toValue;
    }

    /**
     * @param node the node to which the transition applies
     */
    public void setNode(E node) {
        this.node = node;
    }

    /**
     * @param duration the duration of the transition to set
     * @see Duration
     */
    public void setDuration(@NonNull Duration duration) {
        this.setCycleDuration(duration);
    }

    
    // --- Commands --------------------------------------------------------------------------
    
    //@ requires getNode() != null;
    @Override
    protected abstract void interpolate(double frac);
    
}
