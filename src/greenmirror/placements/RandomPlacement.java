package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A placement that is random on the relevant object. Internally, it is replaced by GreenMirror
 * by a {@link CustomPlacement} so the placement won't be recalculated again and again.
 * 
 * @author Karim El Assal
 */
public class RandomPlacement extends Placement {
    
    @Override @NonNull
    public RandomPlacement clone() {
        return ((RandomPlacement) new RandomPlacement().withData(toData()));
    }
}