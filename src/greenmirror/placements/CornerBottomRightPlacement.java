package greenmirror.placements;

import greenmirror.Placement;

public class CornerBottomRightPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public CornerBottomRightPlacement clone() {
        return ((CornerBottomRightPlacement) new CornerBottomRightPlacement().withData(toData()));
    }
}