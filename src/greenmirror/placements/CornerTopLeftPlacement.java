package greenmirror.placements;

import greenmirror.Placement;

public class CornerTopLeftPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public CornerTopLeftPlacement clone() {
        return ((CornerTopLeftPlacement) new CornerTopLeftPlacement().withData(toData()));
    }
}