package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class CornerTopLeftPlacement extends Placement {
    
    @Override @NonNull
    public CornerTopLeftPlacement clone() {
        return ((CornerTopLeftPlacement) new CornerTopLeftPlacement().withData(toData()));
    }
}