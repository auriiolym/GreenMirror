package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} on the bottom right corner.
 * 
 * @author Karim El Assal
 */
public class CornerBottomRightPlacement extends Placement {
    
    @Override @NonNull
    public CornerBottomRightPlacement clone() {
        return ((CornerBottomRightPlacement) new CornerBottomRightPlacement().withData(toData()));
    }
}