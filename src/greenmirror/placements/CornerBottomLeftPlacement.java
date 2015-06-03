package greenmirror.placements;

import greenmirror.Placement;

public class CornerBottomLeftPlacement extends Placement {
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public CornerBottomLeftPlacement clone() {
        return ((CornerBottomLeftPlacement) new CornerBottomLeftPlacement().withData(toData()));
    }
}