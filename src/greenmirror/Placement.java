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
    EDGE_LEFT_MIDDLE, 
    EDGE_RIGHT_MIDDLE;

    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The relative position to the selected <tt>Placement</tt>. If Placement.CUSTOM is chosen,
     * it should default to Placement.MIDDLE. This means that when choosing Placement.CUSTOM,
     * a <tt>RelativePosition</tt> should be set.
     */
    //@ private invariant position != null;
    private RelativePoint position = new RelativePoint(0, 0);

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The relative position.
     */
    //@ ensures \result != null;
    /*@ pure */ public RelativePoint getRelativePosition() {
        return position;
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
     * @param position The relative position to set.
     * @return         <tt>this</tt>
     */
    public Placement setRelativePosition(RelativePoint position) {
        this.position = position;
        return this;
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
                p.setRelativePosition(new RelativePoint(
                                Double.valueOf(dataParts[1]), 
                                Double.valueOf(dataParts[2])));
                return p;
            }
        }
        return null;
    }
    
    /**
     * An auxillary type to handle relative positions.
     * 
     * @author Karim El Assal
     */
    public static class RelativePoint extends Point3D {
        
        /**
         * Explicitly copy the constructor of the superclass.
         * @param posX The x position.
         * @param posY The y position.
         */
        //@ ensures getX() == posX && getY() == posY;
        public RelativePoint(double posX, double posY) {
            super(posX, posY, 0);
        }
    }
}