package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} in the exact middle.
 * 
 * @author Karim El Assal
 */
public class MiddlePlacement extends Placement {
    
    @Override @NonNull
    public MiddlePlacement clone() {
        return ((MiddlePlacement) new MiddlePlacement().withData(toData()));
    }
}