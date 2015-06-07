package greenmirror.placements;

import greenmirror.Placement;

import org.eclipse.jdt.annotation.NonNull;

/**
 * A custom placement that relies on the relative position values. They are relative with
 * respect to the middle point of the <code>Node</code>.
 * 
 * @author Karim El Assal
 */
public class CustomPlacement extends Placement {

    /**
     * Creates a new <code>Placement</code> without any more relative position information.
     */
    public CustomPlacement() {}
    
    /**
     * Creates a new <code>Placement</code> with relative x and y position information. 
     * 
     * @param posX the x coordinate relative to this <code>Placement</code>
     * @param posY the y coordinate relative to this <code>Placement</code>
     */
    //@ ensures getRelativePosition().getX() == posX && getRelativePosition().getY() == posY;
    public CustomPlacement(double posX, double  posY) {
        withRelativePosition(posX, posY);
    }

    /**
     * Creates a new <code>Placement</code> with relative x, y and z position information. 
     * 
     * @param posX the x coordinate relative to this <code>Placement</code>
     * @param posY the y coordinate relative to this <code>Placement</code>
     * @param posZ the z coordinate relative to this <code>Placement</code>
     */
    //@ ensures getRelativePosition().getX() == posX && getRelativePosition().getY() == posY;
    //@ ensures getRelativePosition().getZ() == posZ;
    public CustomPlacement(double posX, double posY, double posZ) {
        withRelativePosition(posX, posY, posZ);
    }
    
    @Override @NonNull
    public CustomPlacement clone() {
        return ((CustomPlacement) new CustomPlacement().withData(toData()));
    }
}