package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} on the top right corner.
 * 
 * @author Karim El Assal
 */
public class CornerTopRightPlacement extends Placement {
    
    @Override @NonNull
    public CornerTopRightPlacement clone() {
        return ((CornerTopRightPlacement) new CornerTopRightPlacement().withData(toData()));
    }
}