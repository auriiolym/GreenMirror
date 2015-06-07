package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class EdgeRightPlacement extends Placement {
    
    
    @Override @NonNull
    public EdgeRightPlacement clone() {
        return ((EdgeRightPlacement) new EdgeRightPlacement().withData(toData()));
    }
}