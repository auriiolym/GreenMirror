package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} centered on the left edge.
 * 
 * @author Karim El Assal
 */
public class EdgeLeftPlacement extends Placement {
    
    @Override @NonNull
    public EdgeLeftPlacement clone() {
        return ((EdgeLeftPlacement) new EdgeLeftPlacement().withData(toData()));
    }
}