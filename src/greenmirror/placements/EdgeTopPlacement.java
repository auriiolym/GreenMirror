package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class EdgeTopPlacement extends Placement {
    
    @Override @NonNull
    public EdgeTopPlacement clone() {
        return ((EdgeTopPlacement) new EdgeTopPlacement().withData(toData()));
    }
}