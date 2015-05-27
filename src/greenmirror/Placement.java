package greenmirror;

import java.util.LinkedList;
import java.util.List;
import java.util.ServiceLoader;

import javafx.geometry.Point3D;

/**
 * The <tt>Placement</tt> abstract class used for indicating where a <tt>Node</tt> 
 * should be placed relative to another <tt>Node</tt>.
 * 
 * If you want to use just the placement information, use The singleton Placement.SUBCLASS. E.g.:
 * <tt>Placement.MIDDLE</tt>. If you want to use extra, relative position information, create
 * a new instance of a subclass, like: <tt>new Placement.Middle()</tt>.
 * The <tt>Custom</tt> subclass does not have a singleton, because extra, relative position 
 * information must be given.
 * 
 * @author Karim El Assal
 */
public abstract class Placement implements Cloneable {
    
    // -- Class variables --------------------------------------------------------------------

    /** The prototypes of all <tt>Placement</tt>s. */
    private static List<Placement> prototypes = new LinkedList<>();
    
    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The relative position to the selected <tt>Placement</tt>. If Placement.CUSTOM is chosen,
     * it should default to Placement.MIDDLE. This means that when choosing Placement.CUSTOM,
     * a relative position should be set.
     */
    //@ private invariant relativePosition != null;
    private Point3D relativePosition = new Point3D(0, 0, 0);
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>Placement</tt> without any more relative position information.
     */
    public Placement() {}
    
    /**
     * Create a new <tt>Placement</tt> with more relative position information.
     * @param posX The x coordinate relative to this <tt>Placement</tt>.
     * @param posY The y coordinate relative to this <tt>Placement</tt>.
     */
    public Placement(double posX, double  posY) {
        withRelativePosition(posX, posY);
    }

    /**
     * Create a new <tt>Placement</tt> with more relative position information.
     * @param posX The x coordinate relative to this <tt>Placement</tt>.
     * @param posY The y coordinate relative to this <tt>Placement</tt>.
     * @param posZ The z coordinate relative to this <tt>Placement</tt>.
     */
    public Placement(double posX, double posY, double posZ) {
        withRelativePosition(posX, posY, posZ);
    }

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The relative position.
     */
    //@ ensures \result != null;
    /*@ pure */ public Point3D getRelativePosition() {
        return relativePosition;
    }
    
    /**
     * @return The name of this placement.
     */
    //@ ensures \result != null;
    /*@ pure */ public String toString() {
        return getClass().getSimpleName();
    }
    
    /**
     * @return A plain data representation.
     */
    //@ ensures \result != null;
    /*@ pure */ public String toData() {
        return toString() + ":" 
                + getRelativePosition().getX() + ":" 
                + getRelativePosition().getY() + ":"
                + getRelativePosition().getZ();
    }
    
    /**
     * @return A deep copy of this <tt>Placement</tt>.
     */
    //@ ensures \result != null;
    /*@ pure */ public abstract Placement clone();
    
    /**
     * Check if <tt>object</tt> is the same as <tt>this</tt> according to the type of 
     * placement and relative position.
     * @param object The object to check.
     * @return       <tt>true</tt> if the placement type and relative position are the same.
     */
    @Override
    /*@ pure */ public boolean equals(Object object) {
        if (object == null || !(object instanceof Placement)) {
            return false;
        }
        return toData().equals(((Placement) object).toData());
    }
    

    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param relativePosition The relative position to set.
     * @return                 <tt>this</tt>
     */
    //@ ensures getRelativePosition() == relativePosition;
    //@ ensures \result == this;
    public Placement withRelativePosition(Point3D relativePosition) {
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
    public Placement withRelativePosition(double posX, double posY) {
        return withRelativePosition(posX, posY, 0);
    }
    
    /**
     * @param posX The relative x coordinate.
     * @param posY The relative y coordinate.
     * @param posY The relative z coordinate.
     * @return     <tt>this</tt>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, posZ));
    //@ ensures \result == this;
    public Placement withRelativePosition(double posX, double posY, double posZ) {
        return withRelativePosition(new Point3D(posX, posY, posZ));
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
        if (dataParts.length != 4) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        
        retrievePlacements();
        
        for (Placement p : getPrototypes()) {
            if (p.toString().equals(dataParts[0])) {
                return p.clone().withRelativePosition(new Point3D(
                                    Double.valueOf(dataParts[1]), 
                                    Double.valueOf(dataParts[2]),
                                    Double.valueOf(dataParts[3])));
            }
        }
        return null;
    }
    
    /**
     * @return The prototypes of all available <tt>Placement</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ private static List<Placement> getPrototypes() {
        return prototypes;
    }
    
    /**
     * Retrieve all available <tt>Placement</tt>s.
     */
    //@ ensures getPrototypes().size() > 0;
    private static void retrievePlacements() {
        if (getPrototypes().size() == 0) {
            ServiceLoader.load(Placement.class).forEach(pm -> {
                getPrototypes().add(pm);
            });
        }
    }
    
    
    
    public static final Placement NONE = new None();

    public static class None extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public None clone() {
            return new None();
        }
    }
    
    
    public static final Placement RANDOM = new Random();
    
    public static class Random extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public Random clone() {
            return new Random();
        }
    }
    
    
    
    public static class Custom extends Placement {

        public Custom() {
            super();
        }
        
        public Custom(double posX, double  posY) {
            super(posX, posY);
        }
        
        public Custom(double posX, double posY, double posZ) {
            super(posX, posY, posZ);
        }
        
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public Custom clone() {
            return new Custom();
        }
    }
    
    
    public static final Placement MIDDLE = new Middle();
    
    public static class Middle extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public Middle clone() {
            return new Middle();
        }
    }
    
    
    public static final Placement EDGE_TOP = new EdgeTop();
    
    public static class EdgeTop extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public EdgeTop clone() {
            return new EdgeTop();
        }
    }
    
    
    public static final Placement EDGE_RIGHT = new EdgeRight();
    
    public static class EdgeRight extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public EdgeRight clone() {
            return new EdgeRight();
        }
    }
    
    
    public static final Placement EDGE_BOTTOM = new EdgeBottom();
    
    public static class EdgeBottom extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public EdgeBottom clone() {
            return new EdgeBottom();
        }
    }
    
    
    public static final Placement EDGE_LEFT = new EdgeLeft();
    
    public static class EdgeLeft extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public EdgeLeft clone() {
            return new EdgeLeft();
        }
    }
    
    
    public static final Placement CORNER_TOP_LEFT = new CornerTopLeft();
    
    public static class CornerTopLeft extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public CornerTopLeft clone() {
            return new CornerTopLeft();
        }
    }
    
    
    public static final Placement CORNER_TOP_RIGHT = new CornerTopRight();
    
    public static class CornerTopRight extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public CornerTopRight clone() {
            return new CornerTopRight();
        }
    }
    
    
    public static final Placement CORNER_BOTTOM_RIGHT = new CornerBottomRight();    
    
    public static class CornerBottomRight extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public CornerBottomRight clone() {
            return new CornerBottomRight();
        }
    }
    
    
    public static final Placement CORNER_BOTTOM_LEFT = new CornerBottomLeft();
    
    public static class CornerBottomLeft extends Placement {
        /* (non-Javadoc)
         * @see greenmirror.Placement#clone()
         */
        @Override
        public CornerBottomLeft clone() {
            return new CornerBottomLeft();
        }
    }
}