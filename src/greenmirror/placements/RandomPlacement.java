package greenmirror.placements;

import greenmirror.Placement;

/**
 * Wordt omgezet in een custom
 * 
 * @author Karim El Assal
 */
public class RandomPlacement extends Placement {
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public RandomPlacement clone() {
        return ((RandomPlacement) new RandomPlacement().withData(toData()));
    }
}