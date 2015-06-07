package greenmirror.placements;

import greenmirror.Placement;
import org.eclipse.jdt.annotation.NonNull;

/**
 * A placement type that indicates that something should be placed on the edge of something else
 * at a specific angle. The angle is given in degrees and the zero-angle start at the exact top.
 * On a clock this would be the on the number 12. A positive angle means turning clockwise.
 * 
 * @author Karim El Assal
 */
public class EdgePlacement extends Placement {
    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the angle in degrees */
    private double angle = 0;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /** Creates an EdgePlacement with a zero angle */
    public EdgePlacement() {}
    
    /**
     * Creates an EdgePlacement with a specific angle
     * 
     * @param angle the angle in degrees; 0 is at the exact top
     */
    public EdgePlacement(double angle) {
        withAngle(angle);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the angle in degrees */
    public double getAngle() {
        return this.angle;
    }
    
    /**
     * Adds the angle to the data.
     * 
     * @return the data of the supertype, but with the angle appended
     */
    @Override @NonNull
    public String toData() {
        return super.toData() + ":" + getAngle();
    }
    
    @Override @NonNull
    public EdgePlacement clone() {
        return ((EdgePlacement) new EdgePlacement().withData(toData()));
    }

    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param angle the angle in degrees, starting at the exact top and going clockwise in the 
     *              positive direction
     * @return      <code>this</code>
     */
    @NonNull public EdgePlacement withAngle(double angle) {
        if (angle < 0) {
            angle = 360 + angle;
        }
        this.angle = angle % 360;
        return this;
    }
    
    /**
     * Also extracts the angle from the data. If the angle wasn't found, use 0.
     * 
     * @param data the data
     * @return     <code>this</code>
     */
    @Override @NonNull
    public EdgePlacement withData(@NonNull String data) {
        super.withData(data);
        final String[] dataParts = data.split(":");
        if (dataParts.length < 4) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        return withAngle(dataParts.length >= 5 ? Double.valueOf(dataParts[4]) : 0);
    }
}