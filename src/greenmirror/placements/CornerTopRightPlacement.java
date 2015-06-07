package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class CornerTopRightPlacement extends Placement {
    
    @Override @NonNull
    public CornerTopRightPlacement clone() {
        return ((CornerTopRightPlacement) new CornerTopRightPlacement().withData(toData()));
    }
}