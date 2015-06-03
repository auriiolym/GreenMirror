package greenmirror.placements;

import greenmirror.Placement;

public class CornerTopRightPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public CornerTopRightPlacement clone() {
        return ((CornerTopRightPlacement) new CornerTopRightPlacement().withData(toData()));
    }
}