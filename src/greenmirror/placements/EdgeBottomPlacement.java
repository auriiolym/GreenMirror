package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} centered on the bottom edge.
 * 
 * @author Karim El Assal
 */
public class EdgeBottomPlacement extends Placement {
    
    @Override @NonNull
    public EdgeBottomPlacement clone() {
        return ((EdgeBottomPlacement) new EdgeBottomPlacement().withData(toData()));
    }
}