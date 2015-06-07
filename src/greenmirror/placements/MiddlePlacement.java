package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

public class MiddlePlacement extends Placement {
    
    @Override @NonNull
    public MiddlePlacement clone() {
        return ((MiddlePlacement) new MiddlePlacement().withData(toData()));
    }
}