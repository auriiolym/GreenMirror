package greenmirror.placements;

import greenmirror.Placement;

public class EdgeRightPlacement extends Placement {
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public EdgeRightPlacement clone() {
        return ((EdgeRightPlacement) new EdgeRightPlacement().withData(toData()));
    }
}