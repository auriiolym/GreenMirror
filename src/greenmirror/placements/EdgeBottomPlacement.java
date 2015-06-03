package greenmirror.placements;

import greenmirror.Placement;

public class EdgeBottomPlacement extends Placement {
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public EdgeBottomPlacement clone() {
        return ((EdgeBottomPlacement) new EdgeBottomPlacement().withData(toData()));
    }
}