package greenmirror.placements;

import greenmirror.Placement;

public class EdgeTopPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public EdgeTopPlacement clone() {
        return ((EdgeTopPlacement) new EdgeTopPlacement().withData(toData()));
    }
}