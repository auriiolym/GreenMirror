package greenmirror;

import javafx.geometry.Point3D;

/**
 * The <tt>Placement</tt> enumeration used for indicating where a <tt>Node</tt> 
 * should be placed relative to another <tt>Node</tt>.
 * 
 * @author Karim El Assal
 */
public enum Placement {
    NONE,
    RANDOM, 
    CUSTOM, 
    MIDDLE, 
    EDGE_TOP,
    EDGE_RIGHT,
    EDGE_BOTTOM,
    EDGE_LEFT, 
    CORNER_TOP_LEFT,
    CORNER_TOP_RIGHT,
    CORNER_BOTTOM_RIGHT,
    CORNER_BOTTOM_LEFT,
    ;

    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The relative position to the selected <tt>Placement</tt>. If Placement.CUSTOM is chosen,
     * it should default to Placement.MIDDLE. This means that when choosing Placement.CUSTOM,
     * a relative position should be set.
     */
    //@ private invariant relativePosition != null;
    private Point3D relativePosition = new Point3D(0, 0, 0);

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The relative position.
     */
    //@ ensures \result != null;
    /*@ pure */ public Point3D getRelativePosition() {
        return relativePosition;
    }
    
    /**
     * @return A plain data representation.
     */
    //@ ensures \result != null;
    /*@ pure */ public String toData() {
        return name() + ":" + getRelativePosition().getX() + ":" + getRelativePosition().getY();
    }
    

    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param relativePosition The relative position to set.
     * @return         <tt>this</tt>
     */
    //@ ensures getRelativePosition() == relativePosition;
    //@ ensures \result == this;
    public Placement setRelativePosition(Point3D relativePosition) {
        this.relativePosition = relativePosition;
        return this;
    }
    
    /**
     * @param posX The relative x coordinate.
     * @param posY The relative y coordinate.
     * @return     <tt>this</tt>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, 0));
    //@ ensures \result == this;
    public Placement setRelativePosition(double posX, double posY) {
        return setRelativePosition(posX, posY, 0);
    }
    
    /**
     * @param posX The relative x coordinate.
     * @param posY The relative y coordinate.
     * @param posY The relative z coordinate.
     * @return     <tt>this</tt>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, posZ));
    //@ ensures \result == this;
    public Placement setRelativePosition(double posX, double posY, double posZ) {
        return setRelativePosition(new Point3D(posX, posY, posZ));
    }
    

    // -- Class usage ------------------------------------------------------------------------

    /**
     * @param data The requested <tt>Placement</tt>.
     * @return     A <tt>Placement</tt> according to <tt>data</tt>; <tt>null</tt> if none was
     *             found.
     * @throws IllegalArgumentException     If <tt>data</tt> was invalid.
     */
    //@ requires data != null;
    public static Placement fromData(String data) {
        String[] dataParts = data.split(":");
        if (dataParts.length != 3) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        
        for (Placement p : values()) {
            if (p.name().equals(dataParts[0])) {
                p.setRelativePosition(new Point3D(
                                Double.valueOf(dataParts[1]), 
                                Double.valueOf(dataParts[2]), 0));
                return p;
            }
        }
        return null;
    }
}