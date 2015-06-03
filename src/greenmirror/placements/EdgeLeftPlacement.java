package greenmirror.placements;

import greenmirror.Placement;

public class EdgeLeftPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public EdgeLeftPlacement clone() {
        return ((EdgeLeftPlacement) new EdgeLeftPlacement().withData(toData()));
    }
}