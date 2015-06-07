package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

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