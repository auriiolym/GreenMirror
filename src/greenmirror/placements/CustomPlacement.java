package greenmirror.placements;

import greenmirror.Placement;

public class CustomPlacement extends Placement {

    public CustomPlacement() {
        super();
    }
    
    public CustomPlacement(double posX, double  posY) {
        super(posX, posY);
    }
    
    public CustomPlacement(double posX, double posY, double posZ) {
        super(posX, posY, posZ);
    }
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public CustomPlacement clone() {
        return ((CustomPlacement) new CustomPlacement().withData(toData()));
    }
}