package greenmirror;

import greenmirror.placements.CornerBottomLeftPlacement;
import greenmirror.placements.CornerBottomRightPlacement;
import greenmirror.placements.CornerTopLeftPlacement;
import greenmirror.placements.CornerTopRightPlacement;
import greenmirror.placements.EdgeBottomPlacement;
import greenmirror.placements.EdgeLeftPlacement;
import greenmirror.placements.EdgeRightPlacement;
import greenmirror.placements.EdgeTopPlacement;
import greenmirror.placements.MiddlePlacement;
import greenmirror.placements.NoPlacement;
import greenmirror.placements.RandomPlacement;

import java.util.LinkedList;
import java.util.List;
import java.util.ServiceLoader;

import javafx.geometry.Point3D;

/**
 * The <code>Placement</code> abstract class used for indicating where a <code>Node</code> 
 * should be placed relative to another <code>Node</code>.
 * 
 * If you want to use just the placement information, use The singleton Placement.SUBCLASS. E.g.:
 * <code>Placement.MIDDLE</code>. If you want to use extra, relative position information, create
 * a new instance of a subclass, like: <code>new Placement.Middle()</code>.
 * The <code>Custom</code> subclass does not have a singleton, because extra, relative position 
 * information must be given.
 * 
 * @author Karim El Assal
 */
public abstract class Placement implements Cloneable {
    
    // -- Class variables --------------------------------------------------------------------

    /** The prototypes of all <code>Placement</code>s. */
    private static List<Placement> prototypes = new LinkedList<Placement>();
    
    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The relative position to the selected <code>Placement</code>. If Placement.CUSTOM is chosen,
     * it should default to Placement.MIDDLE. This means that when choosing Placement.CUSTOM,
     * a relative position should be set.
     */
    //@ private invariant relativePosition != null;
    private Point3D relativePosition = Point3D.ZERO;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <code>Placement</code> without any more relative position information.
     */
    public Placement() {}
    
    /**
     * Create a new <code>Placement</code> with more relative position information.
     * @param posX The x coordinate relative to this <code>Placement</code>.
     * @param posY The y coordinate relative to this <code>Placement</code>.
     */
    //TODO: remove this and implement the same functionality at CustomPlacement.
    public Placement(double posX, double  posY) {
        withRelativePosition(posX, posY);
    }

    /**
     * Create a new <code>Placement</code> with more relative position information.
     * @param posX The x coordinate relative to this <code>Placement</code>.
     * @param posY The y coordinate relative to this <code>Placement</code>.
     * @param posZ The z coordinate relative to this <code>Placement</code>.
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
        return getClass().getSimpleName().replace("Placement", "");
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
     * @return A deep copy of this <code>Placement</code>.
     */
    //@ ensures \result != null;
    /*@ pure */ public abstract Placement clone();
    
    /**
     * Check if <code>object</code> is the same as <code>this</code> according to the type of 
     * placement and relative position.
     * @param object The object to check.
     * @return       <code>true</code> if the placement type and relative position are the same.
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
     * @return                 <code>this</code>
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
     * @return     <code>this</code>
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
     * @return     <code>this</code>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, posZ));
    //@ ensures \result == this;
    public Placement withRelativePosition(double posX, double posY, double posZ) {
        return withRelativePosition(new Point3D(posX, posY, posZ));
    }
    
    public Placement withData(String data) {
        String[] dataParts = data.split(":");
        if (dataParts.length < 4) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        
        withRelativePosition(new Point3D(
                Double.valueOf(dataParts[1]), 
                Double.valueOf(dataParts[2]),
                Double.valueOf(dataParts[3])));
        return this;
    }
    

    // -- Class usage ------------------------------------------------------------------------

    /**
     * @param data The requested <code>Placement</code>.
     * @return     A <code>Placement</code> according to <code>data</code>; <code>null</code> if none was
     *             found.
     * @throws IllegalArgumentException     If <code>data</code> was invalid.
     */
    //@ requires data != null;
    public static Placement fromData(String data) {
        if (!data.contains(":")) {
            throw new IllegalArgumentException("The passed placement data was invalid.");
        }
        String[] dataParts = data.split(":", 2);
        
        retrievePlacements();
        
        for (Placement p : getPrototypes()) {
            if (p.toString().equals(dataParts[0])) {
                return p.clone().withData(data);
            }
        }
        return null;
    }
    
    /**
     * @return The prototypes of all available <code>Placement</code>s.
     */
    //@ ensures \result != null;
    /*@ pure */ private static List<Placement> getPrototypes() {
        return prototypes;
    }
    
    /**
     * Retrieve all available <code>Placement</code>s.
     */
    //@ ensures getPrototypes().size() > 0;
    private static void retrievePlacements() {
        if (getPrototypes().size() == 0) {
            for (Placement pm : ServiceLoader.load(Placement.class)) {
                getPrototypes().add(pm);
            };
        }
    }
    
    
    
    public static final Placement NONE = new NoPlacement();
    
    public static final Placement RANDOM = new RandomPlacement();
    
    public static final Placement MIDDLE = new MiddlePlacement();
        
    public static final Placement EDGE_TOP = new EdgeTopPlacement();
    
    public static final Placement EDGE_RIGHT = new EdgeRightPlacement();
        
    public static final Placement EDGE_BOTTOM = new EdgeBottomPlacement();
    
    public static final Placement EDGE_LEFT = new EdgeLeftPlacement();
    
    public static final Placement CORNER_TOP_LEFT = new CornerTopLeftPlacement();
    
    public static final Placement CORNER_TOP_RIGHT = new CornerTopRightPlacement();
    
    public static final Placement CORNER_BOTTOM_RIGHT = new CornerBottomRightPlacement();    
    
    public static final Placement CORNER_BOTTOM_LEFT = new CornerBottomLeftPlacement();
    

}