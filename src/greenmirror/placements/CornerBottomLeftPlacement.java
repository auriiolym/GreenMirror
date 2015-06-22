package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} on the bottom left corner.
 * 
 * @author Karim El Assal
 */
public class CornerBottomLeftPlacement extends Placement {
    
    @Override @NonNull 
    public CornerBottomLeftPlacement clone() {
        return ((CornerBottomLeftPlacement) new CornerBottomLeftPlacement().withData(toData()));
    }
}