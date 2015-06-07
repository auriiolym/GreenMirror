package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class EdgeLeftPlacement extends Placement {
    
    @Override @NonNull
    public EdgeLeftPlacement clone() {
        return ((EdgeLeftPlacement) new EdgeLeftPlacement().withData(toData()));
    }
}