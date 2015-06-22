package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A {@link greenmirror.Placement} that indicates no placement.
 * 
 * @author Karim El Assal
 */
public class NoPlacement extends Placement {
    
    @Override @NonNull
    public String toString() {
        return "None";
    }
    
    @Override @NonNull
    public NoPlacement clone() {
        return new NoPlacement();
    }
}