package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} centered on the right edge.
 * 
 * @author Karim El Assal
 */
public class EdgeRightPlacement extends Placement {
    
    @Override @NonNull
    public EdgeRightPlacement clone() {
        return ((EdgeRightPlacement) new EdgeRightPlacement().withData(toData()));
    }
}