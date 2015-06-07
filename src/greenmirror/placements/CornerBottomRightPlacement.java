package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class CornerBottomRightPlacement extends Placement {
    
    @Override @NonNull
    public CornerBottomRightPlacement clone() {
        return ((CornerBottomRightPlacement) new CornerBottomRightPlacement().withData(toData()));
    }
}