package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} on the top left corner.
 * 
 * @author Karim El Assal
 */
public class CornerTopLeftPlacement extends Placement {
    
    @Override @NonNull
    public CornerTopLeftPlacement clone() {
        return ((CornerTopLeftPlacement) new CornerTopLeftPlacement().withData(toData()));
    }
}