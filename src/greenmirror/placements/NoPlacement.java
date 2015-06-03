package greenmirror.placements;

import greenmirror.Placement;

public class NoPlacement extends Placement {
    
    @Override
    public String toString() {
        return "None";
    }
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public NoPlacement clone() {
        return new NoPlacement();
    }
}