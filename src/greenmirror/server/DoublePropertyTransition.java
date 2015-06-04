package greenmirror.server;

import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public abstract class DoublePropertyTransition<E extends javafx.scene.Node>
    extends AbstractTransition<E, Double> {

    // --- Instance variables ----------------------------------------------------------------
    
    // --- Constructors ----------------------------------------------------------------------
    
    public DoublePropertyTransition(Duration duration, E node, Double toValue) {
        super(duration, node, toValue);
    }
    
    // --- Queries ---------------------------------------------------------------------------
    
    // --- Setters ---------------------------------------------------------------------------
    
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
    
    protected abstract Double getPropertyValue();
    
    protected abstract void setPropertyValue(Double value);
    
}
