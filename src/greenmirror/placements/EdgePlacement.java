package greenmirror.placements;

import greenmirror.Placement;

public class EdgePlacement extends Placement {
    
    private double angle = 0;
    
    public EdgePlacement() {
        
    }
    
    public EdgePlacement(double angle) {
        withAngle(angle);
    }
    
    public double getAngle() {
        return this.angle;
    }
    
    /**
     * @param angle Angle in degrees.
     * @return      <code>this</code>
     */
    public EdgePlacement withAngle(double angle) {
        if (angle < 0) {
            angle = 360 + angle;
        }
        this.angle = angle % 360;
        return this;
    }
    
    @Override
    public EdgePlacement withData(String data) {
        super.withData(data);
        String[] dataParts = data.split(":");
        if (dataParts.length < 4) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        return withAngle(Double.valueOf(dataParts[3]));
    }
    
    @Override
    public String toData() {
        return super.toData() + ":" + getAngle();
    }
    
    /* (non-Javadoc)
     * @see greenmirror.Placement#clone()
     */
    @Override
    public EdgePlacement clone() {
        return ((EdgePlacement) new EdgePlacement().withData(toData()));
    }
}