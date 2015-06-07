package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class EdgeBottomPlacement extends Placement {
    
    
    @Override @NonNull
    public EdgeBottomPlacement clone() {
        return ((EdgeBottomPlacement) new EdgeBottomPlacement().withData(toData()));
    }
}