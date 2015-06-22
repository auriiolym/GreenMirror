package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} centered on the top edge.
 * 
 * @author Karim El Assal
 */
public class EdgeTopPlacement extends Placement {
    
    @Override @NonNull
    public EdgeTopPlacement clone() {
        return ((EdgeTopPlacement) new EdgeTopPlacement().withData(toData()));
    }
}