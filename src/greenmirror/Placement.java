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