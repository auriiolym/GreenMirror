package greenmirror.placements;

import greenmirror.Placement;

public class MiddlePlacement extends Placement {
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public MiddlePlacement clone() {
        return ((MiddlePlacement) new MiddlePlacement().withData(toData()));
    }
}