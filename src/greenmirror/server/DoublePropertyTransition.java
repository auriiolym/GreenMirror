package greenmirror.server;

import org.eclipse.jdt.annotation.NonNull;

import javafx.util.Duration;

/**
 * A more concrete extension of {@link AbstractTransition}. Only the constructor(s), and the
 * get and set methods of a <code>Double</code> property have to be implemented in a subclass.
 * This class makes sure all properties that are of the <code>Double</code> type are animated
 * the same way: if no starting value is set, it is retrieved from the node when the transition
 * starts.
 * 
 * @author Karim El Assal
 */
public abstract class DoublePropertyTransition<E extends javafx.scene.Node>
    extends AbstractTransition<E, Double> {
    

    // --- Constructors ----------------------------------------------------------------------    
    
    /**
     * @param duration the duration of the transition
     * @param node     the node to which the transition applies
     * @param toValue  the 'to' value
     * @see            AbstractTransition#AbstractTransition(Duration, javafx.scene.Node, Object)
     */
    public DoublePropertyTransition(@NonNull Duration duration, E node, Double toValue) {
        super(duration, node, toValue);
    }
    
    
    // --- Queries ---------------------------------------------------------------------------

    /**
     * Returns the current value of the property that has to be animated. Usually this just
     * returns the result of the getter of the property.
     * 
     * @return the current property value
     */
    /*@ pure */ protected abstract Double getPropertyValue();
    
    
    // --- Setters ---------------------------------------------------------------------------
    
    /**
     * Sets the property value. This is while the transition is playing. Usually this just
     * passes the value on to the setter of the property.
     * 
     * @param value the new value
     */
    //@ ensures getPropertyValue() == value;
    protected abstract void setPropertyValue(@NonNull Double value);
    
    
    // --- Commands --------------------------------------------------------------------------
    
    //@ requires getNode() != null;
    @Override
    protected void interpolate(double frac) {
        if (getFromValue() == null) {
            setFromValue(getPropertyValue());
        }
        
        final Double valueDiff = getToValue() - getFromValue();
        setPropertyValue(getFromValue() + valueDiff * frac);
    }
}
