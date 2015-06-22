package greenmirror.fxpropertywrappers;

import greenmirror.FxPropertyWrapper;
import org.eclipse.jdt.annotation.NonNull;

import javafx.scene.paint.Paint;

/**
 * A wrapper for the <code>Paint</code> type of FX properties.
 * 
 * @author Karim El Assal
 */
public class PaintFxProperty extends FxPropertyWrapper {

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param propertyName the name of the property
     * @see greenmirror.FxPropertyWrapper#FxPropertyWrapper(String)
     */
    public PaintFxProperty(@NonNull String propertyName) {
        super(propertyName);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull 
    public Class<?> getPropertyType() {
        return Paint.class;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public Paint cast(Object instance) {
        if (instance == null) {
            return null;
        }
        return Paint.valueOf(String.valueOf(instance));
    }

    @Override
    public String castToMapValue(Object instance) {
        if (instance == null) {
            return null;
        }
        return String.valueOf(instance);
    }

}
