package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class CornerBottomLeftPlacement extends Placement {
    
    @Override @NonNull 
    public CornerBottomLeftPlacement clone() {
        return ((CornerBottomLeftPlacement) new CornerBottomLeftPlacement().withData(toData()));
    }
}